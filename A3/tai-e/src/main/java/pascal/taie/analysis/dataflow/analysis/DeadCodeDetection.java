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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.graph.AbstractEdge;

import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        // 1. Reachability Analysis
        Set<Stmt> reachable = new java.util.HashSet<>();
        java.util.Queue<Stmt> queue = new java.util.LinkedList<>();

        Stmt entry = cfg.getEntry();
        if (entry != null) {
            reachable.add(entry);
            queue.add(entry);
        }

        while (!queue.isEmpty()) {
            Stmt curr = queue.poll();
            Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(curr);
            Value val = Value.getNAC();
            if (curr instanceof If ifStmt) {
                val = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
            } else if (curr instanceof SwitchStmt switchStmt) {
                val = constants.getInFact(switchStmt).get(switchStmt.getVar());
            }

            if (val.isConstant()) {
                if (curr instanceof If) {
                    Edge.Kind liveKind = (val.getConstant() != 0) ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE;
                    for (Edge<Stmt> edge : outEdges) {
                        if (edge.getKind() == Edge.Kind.IF_TRUE || edge.getKind() == Edge.Kind.IF_FALSE) {
                            if (edge.getKind() == liveKind) {
                                if (reachable.add(edge.getTarget())) {
                                    queue.add(edge.getTarget());
                                }
                            }
                        } else {
                            if (reachable.add(edge.getTarget())) {
                                queue.add(edge.getTarget());
                            }
                        }
                    }
                } else { // SwitchStmt
                    int constVal = val.getConstant();
                    boolean matched = false;
                    for (Edge<Stmt> edge : outEdges) {
                        if (edge.isSwitchCase()) {
                            if (edge.getCaseValue() == constVal) {
                                if (reachable.add(edge.getTarget())) {
                                    queue.add(edge.getTarget());
                                }
                                matched = true;
                            }
                        } else if (!edge.isSwitchCase() && edge.getKind() != Edge.Kind.SWITCH_DEFAULT) {
                            if (reachable.add(edge.getTarget())) {
                                queue.add(edge.getTarget());
                            }
                        }
                    }
                    if (!matched) {
                        for (Edge<Stmt> edge : outEdges) {
                            if (edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                                if (reachable.add(edge.getTarget())) {
                                    queue.add(edge.getTarget());
                                }
                            }
                        }
                    }
                }
            } else {
                for (Edge<Stmt> edge : outEdges) {
                    if (reachable.add(edge.getTarget())) {
                        queue.add(edge.getTarget());
                    }
                }
            }
        }

        // 2. Dead Code Collection
        for (Stmt stmt : ir) {
            if (!reachable.contains(stmt)) {
                deadCode.add(stmt);
            } else if (stmt instanceof AssignStmt<?, ?> assignStmt) {
                LValue lValue = assignStmt.getLValue();
                if (lValue instanceof Var var) {
                    SetFact<Var> liveOut = liveVars.getOutFact(stmt);
                    if (liveOut != null && !liveOut.contains(var) && hasNoSideEffect(assignStmt.getRValue())) {
                        deadCode.add(stmt);
                    }
                }
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
