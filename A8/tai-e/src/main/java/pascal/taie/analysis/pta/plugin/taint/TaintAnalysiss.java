package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;
    private final TaintConfig config;
    private final Solver solver;
    private final CSManager csManager;
    private final Context emptyContext;
    private final Set<Source> sources;
    private final Set<Sink> sinks;
    private final Set<TaintTransfer> transfers;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        sources = config.getSources();
        sinks = config.getSinks();
        transfers = config.getTransfers();
    }

    /**
     * Called by Solver whenever a method call is resolved.
     */
    public void handleCall(Invoke callSite, Context context, JMethod callee) {
        handleSource(callSite, context, callee);
        handleTransfer(callSite, context, callee);
    }

    private void handleSource(Invoke callSite, Context context, JMethod callee) {
        for (Source source : sources) {
            if (source.method().equals(callee)) {
                Var result = callSite.getResult();
                if (result != null) {
                    Obj taintObj = manager.makeTaint(callSite, source.type());
                    CSVar csResult = csManager.getCSVar(context, result);
                    solver.addObjToPointer(csResult, taintObj);
                }
                break;
            }
        }
    }

    private void handleTransfer(Invoke callSite, Context context, JMethod callee) {
        for (TaintTransfer transfer : transfers) {
            if (transfer.method().equals(callee)) {
                handleOneTransfer(callSite, context, transfer);
            }
        }
    }

    private void handleOneTransfer(Invoke callSite, Context context,
                                   TaintTransfer transfer) {
        int from = transfer.from();
        int to = transfer.to();
        Type type = transfer.type();

        CSVar fromVar = getVar(callSite, context, from);
        if (fromVar == null) return;
        if (fromVar.getPointsToSet() == null) return;

        boolean fromHasTaint = false;
        for (CSObj csObj : fromVar.getPointsToSet()) {
            if (manager.isTaint(csObj.getObject())) {
                fromHasTaint = true;
                break;
            }
        }
        if (!fromHasTaint) return;

        CSVar toVar = getVar(callSite, context, to);
        if (toVar == null) return;

        for (CSObj csObj : fromVar.getPointsToSet()) {
            Obj oldObj = csObj.getObject();
            if (manager.isTaint(oldObj)) {
                Invoke sourceCall = manager.getSourceCall(oldObj);
                Obj newTaint = manager.makeTaint(sourceCall, type);
                solver.addObjToPointer(toVar, newTaint);
            }
        }
    }

    private CSVar getVar(Invoke callSite, Context context, int idx) {
        if (idx == TaintTransfer.RESULT) {
            Var result = callSite.getResult();
            return result != null ? csManager.getCSVar(context, result) : null;
        } else if (idx == TaintTransfer.BASE) {
            if (callSite.isStatic()) return null;
            if (callSite.getInvokeExp() instanceof InvokeInstanceExp iie) {
                return csManager.getCSVar(context, iie.getBase());
            }
            return null;
        } else {
            Var arg = callSite.getInvokeExp().getArg(idx);
            return csManager.getCSVar(context, arg);
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();

        for (CSMethod csMethod : solver.getReachableMethods()) {
            Context methodCtx = csMethod.getContext();
            for (Invoke callSite : getInvokesInMethod(csMethod)) {
                for (Sink sink : sinks) {
                    if (sink.method().equals(
                            callSite.getInvokeExp().getMethodRef().resolve())) {
                        Var argVar = callSite.getInvokeExp().getArg(sink.index());
                        CSVar csArg = csManager.getCSVar(methodCtx, argVar);
                        if (csArg.getPointsToSet() == null) continue;

                        for (CSObj csObj : csArg.getPointsToSet()) {
                            if (manager.isTaint(csObj.getObject())) {
                                Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                                taintFlows.add(new TaintFlow(
                                        sourceCall, callSite, sink.index()));
                            }
                        }
                    }
                }
            }
        }
        return taintFlows;
    }

    private Set<Invoke> getInvokesInMethod(CSMethod csMethod) {
        Set<Invoke> invokes = new java.util.LinkedHashSet<>();
        csMethod.getMethod().getIR().forEach(stmt -> {
            if (stmt instanceof Invoke invoke) {
                invokes.add(invoke);
            }
        });
        return invokes;
    }
}
