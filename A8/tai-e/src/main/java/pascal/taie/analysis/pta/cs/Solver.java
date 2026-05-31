package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;
    private final HeapModel heapModel;
    private final ContextSelector contextSelector;

    private CSManager csManager;
    private CSCallGraph callGraph;
    private PointerFlowGraph pointerFlowGraph;
    private WorkList workList;
    private TaintAnalysiss taintAnalysis;
    private Set<CSMethod> reachableMethods = new HashSet<>();
    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() { return options; }
    public ContextSelector getContextSelector() { return contextSelector; }
    public CSManager getCSManager() { return csManager; }

    public Set<CSMethod> getReachableMethods() { return reachableMethods; }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        reachableMethods = new HashSet<>();
        taintAnalysis = new TaintAnalysiss(this);
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    private void addReachable(CSMethod csMethod) {
        if (!reachableMethods.contains(csMethod)) {
            reachableMethods.add(csMethod);
            StmtProcessor processor = new StmtProcessor(csMethod);
            csMethod.getMethod().getIR().getStmts()
                    .forEach(stmt -> stmt.accept(processor));
        }
    }

    private class StmtProcessor implements StmtVisitor<Void> {
        private final CSMethod csMethod;
        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New stmt) {
            workList.addEntry(
                    csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(
                            csManager.getCSObj(
                                    contextSelector.selectHeapContext(
                                            csMethod, heapModel.getObj(stmt)),
                                    heapModel.getObj(stmt))));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue()));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeContext = contextSelector.selectContext(csCallSite, callee);
                CSMethod calleeMethod = csManager.getCSMethod(calleeContext, callee);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, calleeMethod))) {
                    addReachable(calleeMethod);
                    for (int i = 0; i < callee.getParamCount(); i++) {
                        addPFGEdge(
                                csManager.getCSVar(context, stmt.getInvokeExp().getArg(i)),
                                csManager.getCSVar(calleeContext, callee.getIR().getParam(i)));
                    }
                    if (stmt.getResult() != null) {
                        for (Var retVar : callee.getIR().getReturnVars()) {
                            addPFGEdge(
                                    csManager.getCSVar(calleeContext, retVar),
                                    csManager.getCSVar(context, stmt.getResult()));
                        }
                    }
                }
                taintAnalysis.handleCall(stmt, context, callee);
            }
            return null;
        }
    }

    public void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (source.getPointsToSet() != null
                    && !source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet delta = propagate(pointer, entry.pointsToSet());
            if (pointer instanceof CSVar varPtr) {
                Var var = varPtr.getVar();
                for (CSObj obj : delta) {
                    for (StoreField stmt : var.getStoreFields()) {
                        addPFGEdge(
                                csManager.getCSVar(varPtr.getContext(), stmt.getRValue()),
                                csManager.getInstanceField(obj, stmt.getFieldRef().resolve()));
                    }
                    for (LoadField stmt : var.getLoadFields()) {
                        addPFGEdge(
                                csManager.getInstanceField(obj, stmt.getFieldRef().resolve()),
                                csManager.getCSVar(varPtr.getContext(), stmt.getLValue()));
                    }
                    for (StoreArray stmt : var.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(varPtr.getContext(), stmt.getRValue()),
                                csManager.getArrayIndex(obj));
                    }
                    for (LoadArray stmt : var.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(varPtr.getContext(), stmt.getLValue()));
                    }
                    processCall(varPtr, obj);
                }
            }
        }
    }

    public PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet old = pointer.getPointsToSet();
        if (old == null) {
            pointer.setPointsToSet(pointsToSet);
            for (CSObj obj : pointsToSet) delta.addObject(obj);
        } else {
            for (CSObj obj : pointsToSet) {
                if (old.addObject(obj)) delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    public void addObjToPointer(Pointer pointer, Obj obj) {
        CSObj csObj = csManager.getCSObj(
                contextSelector.getEmptyContext(), obj);
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = PointsToSetFactory.make();
            pointer.setPointsToSet(pts);
        }
        if (pts.addObject(csObj)) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, PointsToSetFactory.make(csObj));
            }
        }
    }

    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke callSite : recv.getVar().getInvokes()) {
            JMethod callee = resolveCallee(recvObj, callSite);
            if (callee == null) continue;
            CallKind kind;
            if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
            else if (callSite.isInterface()) kind = CallKind.INTERFACE;
            else if (callSite.isSpecial()) kind = CallKind.SPECIAL;
            else continue;
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            workList.addEntry(
                    csManager.getCSVar(calleeContext, callee.getIR().getThis()),
                    PointsToSetFactory.make(recvObj));
            CSMethod calleeMethod = csManager.getCSMethod(calleeContext, callee);
            if (callGraph.addEdge(new Edge<>(kind, csCallSite, calleeMethod))) {
                addReachable(calleeMethod);
                for (int i = 0; i < callee.getParamCount(); i++) {
                    addPFGEdge(
                            csManager.getCSVar(recv.getContext(), callSite.getInvokeExp().getArg(i)),
                            csManager.getCSVar(calleeContext, callee.getIR().getParam(i)));
                }
                if (callSite.getResult() != null) {
                    for (Var retVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(
                                csManager.getCSVar(calleeContext, retVar),
                                csManager.getCSVar(recv.getContext(), callSite.getResult()));
                    }
                }
            }
            taintAnalysis.handleCall(callSite, recv.getContext(), callee);
        }
    }

    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}