/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private Set<Stmt> reachableStmts;
    private Set<JMethod> reachableMethods;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        reachableStmts = new HashSet<>();
        reachableMethods = new HashSet<>();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!reachableMethods.contains(method)) {
            reachableMethods.add(method);
            List<Stmt> sm = method.getIR().getStmts();
            reachableStmts.addAll(sm);
            sm.forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            // x = new T()  →  add (pt(x), {obj}) to worklist
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // x = y  →  add PFG edge y → x
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // x = T.f (static field load)  →  add PFG edge T.f → x
            if (stmt.isStatic()) {
                addPFGEdge(
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // T.f = x (static field store)  →  add PFG edge x → T.f
            if (stmt.isStatic()) {
                addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // handle static calls here (instance calls handled in processCall)
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))) {
                    addReachable(callee);
                    // link args → params
                    for (int i = 0; i < callee.getParamCount(); i++) {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i)),
                            pointerFlowGraph.getVarPtr(callee.getIR().getParam(i))
                        );
                    }
                    // link return vars → result
                    if (stmt.getResult() != null) {
                        for (Var retVar : callee.getIR().getReturnVars()) {
                            addPFGEdge(
                                pointerFlowGraph.getVarPtr(retVar),
                                pointerFlowGraph.getVarPtr(stmt.getResult())
                            );
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet delta = propagate(pointer, entry.pointsToSet());
            // if pointer is a variable, handle field/array/call for each new obj
            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    // x.f = y  →  add PFG edge y → obj.f
                    for (StoreField stmt : var.getStoreFields()) {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(stmt.getRValue()),
                            pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve())
                        );
                    }
                    // y = x.f  →  add PFG edge obj.f → y
                    for (LoadField stmt : var.getLoadFields()) {
                        addPFGEdge(
                            pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    }
                    // x[i] = y  →  add PFG edge y → obj[*]
                    for (StoreArray stmt : var.getStoreArrays()) {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(stmt.getRValue()),
                            pointerFlowGraph.getArrayIndex(obj)
                        );
                    }
                    // y = x[i]  →  add PFG edge obj[*] → y
                    for (LoadArray stmt : var.getLoadArrays()) {
                        addPFGEdge(
                            pointerFlowGraph.getArrayIndex(obj),
                            pointerFlowGraph.getVarPtr(stmt.getLValue())
                        );
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke callSite : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, callSite);
            // add this → m_this to worklist
            workList.addEntry(
                pointerFlowGraph.getVarPtr(callee.getIR().getThis()),
                new PointsToSet(recv)
            );
            CallKind kind;
            if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
            else if (callSite.isInterface()) kind = CallKind.INTERFACE;
            else if (callSite.isSpecial()) kind = CallKind.SPECIAL;
            else continue; // skip static (handled in StmtProcessor)
            if (callGraph.addEdge(new Edge<>(kind, callSite, callee))) {
                addReachable(callee);
                // link args → params
                for (int i = 0; i < callee.getParamCount(); i++) {
                    addPFGEdge(
                        pointerFlowGraph.getVarPtr(callSite.getInvokeExp().getArg(i)),
                        pointerFlowGraph.getVarPtr(callee.getIR().getParam(i))
                    );
                }
                // link return vars → result
                if (callSite.getResult() != null) {
                    for (Var retVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(retVar),
                            pointerFlowGraph.getVarPtr(callSite.getResult())
                        );
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
