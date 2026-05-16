package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    private List<StoreField> storeFields;
    private List<StoreArray> storeArrays;

    // 预计算每个 store 语句存的值（解决跨方法时 RHS 变量不可见的问题）
    private Map<StoreField, Value> storeFieldValues;
    private Map<StoreArray, Value> storeArrayValues;
    private Map<StoreArray, Value> storeArrayIndexValues;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);

        storeFields = new ArrayList<>();
        storeArrays = new ArrayList<>();
        for (Stmt stmt : icfg.getNodes()) {
            if (stmt instanceof StoreField sf) {
                storeFields.add(sf);
            } else if (stmt instanceof StoreArray sa) {
                storeArrays.add(sa);
            }
        }

        // 预计算每个 StoreField 存的值
        storeFieldValues = new HashMap<>();
        for (StoreField sf : storeFields) {
            storeFieldValues.put(sf, computeStoreValue(sf));
        }

        storeArrayValues = new HashMap<>();
        for (StoreArray sa : storeArrays) {
            storeArrayValues.put(sa, computeArrayStoreValue(sa));
        }

        storeArrayIndexValues = new HashMap<>();
        for (StoreArray sa : storeArrays) {
            storeArrayIndexValues.put(sa, computeStoreExpValue(
                    sa.getArrayAccess().getIndex(),
                    icfg.getContainingMethodOf(sa)));
        }
    }

    private Value computeStoreExpValue(Var var, JMethod method) {
        if (!ConstantPropagation.canHoldInt(var)) return Value.getUndef();
        if (var.isTempConst()) {
            if (var.getTempConstValue() instanceof IntLiteral intLit) {
                return Value.makeConstant(intLit.getValue());
            }
            return Value.getNAC();
        }
        if (method != null && method.getIR() != null) {
            for (Stmt s : method.getIR()) {
                if (s instanceof DefinitionStmt ds && ds.getLValue() == var) {
                    return ConstantPropagation.evaluate(ds.getRValue(), new CPFact());
                }
            }
            List<Var> params = method.getIR().getParams();
            for (int i = 0; i < params.size(); i++) {
                if (params.get(i) == var) {
                    return computeParamValue(method, i);
                }
            }
        }
        return Value.getUndef();
    }

    /**
     * 顺着 IR 预计算 StoreField 的 RHS 变量的值
     */
    private Value computeStoreValue(StoreField sf) {
        Var rhs = sf.getRValue();
        if (!ConstantPropagation.canHoldInt(rhs)) {
            return Value.getUndef();
        }
        // temp const 直接拿
        if (rhs.isTempConst()) {
            if (rhs.getTempConstValue() instanceof IntLiteral intLit) {
                return Value.makeConstant(intLit.getValue());
            }
            return Value.getNAC();
        }
        // 找 rhs 的定义
        JMethod method = icfg.getContainingMethodOf(sf);
        if (method != null && method.getIR() != null) {
            for (Stmt s : method.getIR()) {
                if (s instanceof DefinitionStmt ds
                        && ds.getLValue() == rhs) {
                    return ConstantPropagation.evaluate(
                            ds.getRValue(), new CPFact());
                }
            }
        }

        // 如果没找到定义，可能是参数 — 顺着调用图找实参值
        if (method != null && method.getIR() != null) {
            List<Var> params = method.getIR().getParams();
            for (int i = 0; i < params.size(); i++) {
                if (params.get(i) == rhs) {
                    return computeParamValue(method, i);
                }
            }
        }

        return Value.getUndef();
    }

    private Value computeArrayStoreValue(StoreArray sa) {
        Var rhs = sa.getRValue();
        if (!ConstantPropagation.canHoldInt(rhs)) return Value.getUndef();
        if (rhs.isTempConst()) {
            if (rhs.getTempConstValue() instanceof IntLiteral intLit) {
                return Value.makeConstant(intLit.getValue());
            }
            return Value.getNAC();
        }
        JMethod method = icfg.getContainingMethodOf(sa);
        if (method != null && method.getIR() != null) {
            for (Stmt s : method.getIR()) {
                if (s instanceof DefinitionStmt ds && ds.getLValue() == rhs) {
                    return ConstantPropagation.evaluate(ds.getRValue(), new CPFact());
                }
            }
            List<Var> params = method.getIR().getParams();
            for (int i = 0; i < params.size(); i++) {
                if (params.get(i) == rhs) {
                    return computeParamValue(method, i);
                }
            }
        }
        return Value.getUndef();
    }

    /**
     * 顺着调用图找参数的值
     */
    private Value computeParamValue(JMethod method, int paramIndex) {
        Value result = Value.getUndef();
        CallGraph<Invoke, JMethod> cg = pta.getCallGraph();
        for (Invoke callSite : cg.getCallersOf(method)) {
            List<Var> args = callSite.getInvokeExp().getArgs();
            if (paramIndex < args.size()) {
                Var arg = args.get(paramIndex);
                Value argVal;
                if (arg.isTempConst()) {
                    if (arg.getTempConstValue() instanceof IntLiteral intLit) {
                        argVal = Value.makeConstant(intLit.getValue());
                    } else {
                        argVal = Value.getNAC();
                    }
                } else {
                    // 找 arg 的定义
                    JMethod caller = cg.getContainerOf(callSite);
                    argVal = Value.getUndef();
                    if (caller != null && caller.getIR() != null) {
                        for (Stmt s : caller.getIR()) {
                            if (s instanceof DefinitionStmt ds
                                    && ds.getLValue() == arg) {
                                argVal = ConstantPropagation.evaluate(
                                        ds.getRValue(), new CPFact());
                                break;
                            }
                        }
                    }
                }
                result = cp.meetValue(result, argVal);
            }
        }
        return result;
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = out.copyFrom(in);

        // 处理字段/数组 store → 更新预计算值（运行时再确认）
        if (stmt instanceof StoreField sf && sf.isStatic()) {
            JField field = sf.getFieldRef().resolve();
            Value actualVal = ConstantPropagation.evaluate(sf.getRValue(), in);
            if (!actualVal.isUndef()) {
                // 运行时知道了更精确的值，更新预计算结果
                storeFieldValues.put(sf, actualVal);
            }
        }

        // 处理 define 变量的语句
        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            if (defStmt.getLValue() instanceof Var var
                    && ConstantPropagation.canHoldInt(var)) {
                Value val;
                if (stmt instanceof LoadField lf) {
                    val = evaluateFieldLoad(lf, in);
                } else if (stmt instanceof LoadArray la) {
                    val = evaluateArrayLoad(la, in);
                } else {
                    val = ConstantPropagation.evaluate(defStmt.getRValue(), in);
                }
                changed |= out.update(var, val);
            }
        }
        return changed;
    }

    private Value evaluateFieldLoad(LoadField lf, CPFact in) {
        JField field = lf.getFieldRef().resolve();
        Value result = Value.getUndef();

        if (lf.isStatic()) {
            for (StoreField sf : storeFields) {
                if (sf.isStatic()
                        && sf.getFieldRef().resolve().equals(field)) {
                    // 用预计算的值，而不是用 load 的 in 去 evaluate
                    Value storeVal = ConstantPropagation.evaluate(sf.getRValue(), in);
                    if (storeVal.isUndef()) {
                        storeVal = storeFieldValues.getOrDefault(sf, Value.getUndef());
                    }
                    result = cp.meetValue(result, storeVal);
                }
            }
        } else {
            Var loadBase = ((InstanceFieldAccess) lf.getRValue()).getBase();
            for (StoreField sf : storeFields) {
                if (sf.isStatic()) continue;
                if (sf.getFieldRef().resolve().equals(field)) {
                    Var storeBase =
                            ((InstanceFieldAccess) sf.getLValue()).getBase();
                    if (isAlias(loadBase, storeBase)) {
                        Value storeVal = ConstantPropagation.evaluate(sf.getRValue(), in);
                        if (storeVal.isUndef()) {
                            storeVal = storeFieldValues.getOrDefault(sf, Value.getUndef());
                        }
                        result = cp.meetValue(result, storeVal);
                    }
                }
            }
        }
        return result;
    }

    private Value evaluateArrayLoad(LoadArray la, CPFact in) {
        Var loadBase = la.getArrayAccess().getBase();
        Value loadIdx = ConstantPropagation.evaluate(
                la.getArrayAccess().getIndex(), in);
        Value result = Value.getUndef();

        for (StoreArray sa : storeArrays) {
            Var storeBase = sa.getArrayAccess().getBase();
            if (!isAlias(loadBase, storeBase)) continue;

            Value storeIdx = ConstantPropagation.evaluate(
                    sa.getArrayAccess().getIndex(), in);
            if (storeIdx.isUndef()) {
                storeIdx = storeArrayIndexValues.getOrDefault(sa, Value.getUndef());
            }
            if (isArrayAlias(loadIdx, storeIdx)) {
                // 用预计算的值代替 evaluate
                Value storeVal = ConstantPropagation.evaluate(sa.getRValue(), in);
                if (storeVal.isUndef()) {
                    storeVal = storeArrayValues.getOrDefault(sa, Value.getUndef());
                }
                result = cp.meetValue(result, storeVal);
            }
        }
        return result;
    }

    private boolean isAlias(Var v1, Var v2) {
        Set<Obj> pts1 = pta.getPointsToSet(v1);
        Set<Obj> pts2 = pta.getPointsToSet(v2);
        for (Obj obj : pts1) {
            if (pts2.contains(obj)) {
                return true;
            }
        }
        return false;
    }

    private boolean isArrayAlias(Value idx1, Value idx2) {
        if (idx1.isNAC() || idx2.isNAC()) {
            return true;
        }
        if (idx1.isConstant() && idx2.isConstant()) {
            return idx1.getConstant() == idx2.getConstant();
        }
        return false;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact newOut = out.copy();
        Stmt stmt = edge.getSource();
        if (stmt instanceof Invoke invoke && invoke.getLValue() != null) {
            newOut.remove(invoke.getLValue());
        }
        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact result = new CPFact();
        Stmt stmt = edge.getSource();
        JMethod callee = edge.getCallee();
        if (stmt instanceof Invoke invoke) {
            List<Var> args = invoke.getInvokeExp().getArgs();
            List<Var> params = callee.getIR().getParams();
            for (int i = 0; i < params.size(); i++) {
                result.update(params.get(i), callSiteOut.get(args.get(i)));
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = new CPFact();
        Stmt callSite = edge.getCallSite();
        if (callSite instanceof Invoke invoke && invoke.getLValue() != null) {
            Var lhs = invoke.getLValue();
            Value retVal = Value.getUndef();
            for (Var retVar : edge.getReturnVars()) {
                retVal = cp.meetValue(retVal, returnOut.get(retVar));
            }
            result.update(lhs, retVal);
        }
        return result;
    }
}