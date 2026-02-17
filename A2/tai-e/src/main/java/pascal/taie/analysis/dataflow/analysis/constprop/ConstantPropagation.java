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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Map;
import java.util.Optional;
import java.util.function.BinaryOperator;
import java.util.stream.Stream;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        IR ir = cfg.getIR();
        if (ir.getThis() != null) {
            fact.update(ir.getThis(), Value.getNAC());
        }
        for (Var param : ir.getParams()) {
            fact.update(param, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(entry -> {
            Var key = entry.getKey();
            if (canHoldInt(key)) {
                Value meet = meetValue(entry.getValue(), target.get(key));
                target.update(key, meet);
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        }
        throw new RuntimeException("meet value rule not matched.");
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = out.copyFrom(in);
        Optional<LValue> def = stmt.getDef();
        if (def.isPresent() && def.get() instanceof Var var) {
            if (canHoldInt(var)) {
                Value val = Value.getNAC();
                if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
                    val = evaluate(defStmt.getRValue(), in);
                }
                changed |= out.update(var, val);
            }
        }
        return changed;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var) {
            if (var.isTempConst()) {
                Literal literal = var.getTempConstValue();
                if (literal instanceof IntLiteral intLiteral) {
                    return Value.makeConstant(intLiteral.getValue());
                }
            }
            return in.get(var);
        } else if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof BinaryExp binExp) {
            Value v1 = evaluate(binExp.getOperand1(), in);
            Value v2 = evaluate(binExp.getOperand2(), in);
            if (v1.isConstant() && v2.isConstant()) {
                int c1 = v1.getConstant();
                int c2 = v2.getConstant();
                BinaryExp.Op op = binExp.getOperator();
                if (op instanceof ArithmeticExp.Op) {
                    return switch ((ArithmeticExp.Op) op) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> c2 == 0 ? Value.getUndef() : Value.makeConstant(c1 / c2);
                        case REM -> c2 == 0 ? Value.getUndef() : Value.makeConstant(c1 % c2);
                    };
                } else if (op instanceof ConditionExp.Op) {
                    boolean res = switch ((ConditionExp.Op) op) {
                        case EQ -> c1 == c2;
                        case NE -> c1 != c2;
                        case LT -> c1 < c2;
                        case GT -> c1 > c2;
                        case LE -> c1 <= c2;
                        case GE -> c1 >= c2;
                    };
                    return Value.makeConstant(res ? 1 : 0);
                } else if (op instanceof ShiftExp.Op) {
                    return switch ((ShiftExp.Op) op) {
                        case SHL -> Value.makeConstant(c1 << c2);
                        case SHR -> Value.makeConstant(c1 >> c2);
                        case USHR -> Value.makeConstant(c1 >>> c2);
                    };
                } else if (op instanceof BitwiseExp.Op) {
                    return switch ((BitwiseExp.Op) op) {
                        case AND -> Value.makeConstant(c1 & c2);
                        case OR -> Value.makeConstant(c1 | c2);
                        case XOR -> Value.makeConstant(c1 ^ c2);
                    };
                }
            } else if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
