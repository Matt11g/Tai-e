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

import java.util.List;

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
        List<Var> vars = cfg.getIR().getParams();
        CPFact boundaryFact = new CPFact();
        for (Var var : vars) {
            if (canHoldInt(var)) boundaryFact.update(var, Value.getNAC());
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
       return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(v1.getConstant());
            else return Value.getNAC();
        }
        return Value.getUndef(); // ??
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        //  OUT[B] = gen_B Union (IN[B] - {(x, _)})
        if (!(stmt instanceof DefinitionStmt<?,?>)) return out.copyFrom(in);
        //DefinitionStmt<?, ?> definitionStmt = (DefinitionStmt<?, ?>) stmt;
        LValue lValue = ((DefinitionStmt<?,?>) stmt).getLValue();
        RValue rValue = ((DefinitionStmt<?,?>) stmt).getRValue();
        if (lValue instanceof Var && canHoldInt((Var) lValue)) {
            CPFact out_copy = in.copy();
            out_copy.update((Var) lValue, evaluate(rValue, in));
//            if (in.keySet().contains((Var) lValue) && in.get((Var) lValue).isConstant() && out_copy.keySet().contains((Var) lValue) && out_copy.get((Var) lValue).isConstant()) {
//                if (in.get((Var) lValue).getConstant() != out_copy.get((Var) lValue).getConstant()) {
//                    out_copy.update((Var) lValue, Value.getNAC());
//                }
//            } /* no need */
            return out.copyFrom(out_copy);
        }
        return out.copyFrom(in); // Other situations: like float type, "o.f = v"
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
        if (exp instanceof Var) return in.get((Var) exp);
        if (exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral) exp).getValue());
        if (exp instanceof BinaryExp) {
            if (exp instanceof ArithmeticExp) {
                Var op1 = ((ArithmeticExp) exp).getOperand1(), op2 = ((ArithmeticExp) exp).getOperand2();
                Value op1Value = in.get(op1), op2Value = in.get(op2);
                ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
                switch (op) {
                    case ADD -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() + op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef(); // x = m(1) + m(2) ??
                    }
                    case SUB -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() - op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case MUL -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() * op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case DIV -> {
                        if (op2Value.isConstant() && op2Value.getConstant() == 0) return Value.getUndef();
                        else if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() / op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case REM -> {
                        if (op2Value.isConstant() && op2Value.getConstant() == 0) return Value.getUndef();
                        else if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() % op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                }
            }
            else if (exp instanceof ConditionExp) {
                Var op1 = ((ConditionExp) exp).getOperand1(), op2 = ((ConditionExp) exp).getOperand2();
                Value op1Value = in.get(op1), op2Value = in.get(op2);
                ConditionExp.Op op = ((ConditionExp) exp).getOperator();
                switch (op) {
                    case EQ -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() == op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case NE -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() != op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case LT -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() < op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case GT -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() > op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case LE -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() <= op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case GE -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() >= op2Value.getConstant() ? 1 : 0);
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                }
            }
            else if (exp instanceof ShiftExp) {
                Var op1 = ((ShiftExp) exp).getOperand1(), op2 = ((ShiftExp) exp).getOperand2();
                Value op1Value = in.get(op1), op2Value = in.get(op2);
                ShiftExp.Op op = ((ShiftExp) exp).getOperator();
                switch (op) {
                    case SHL -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() << op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case SHR -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() >> op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case USHR -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() >>> op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                }
            }
            else if (exp instanceof BitwiseExp) {
                Var op1 = ((BitwiseExp) exp).getOperand1(), op2 = ((BitwiseExp) exp).getOperand2();
                Value op1Value = in.get(op1), op2Value = in.get(op2);
                BitwiseExp.Op op = ((BitwiseExp) exp).getOperator();
                switch (op) {
                    case OR -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() | op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case AND -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() & op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                    case XOR -> {
                        if (op1Value.isConstant() && op2Value.isConstant()) return Value.makeConstant(op1Value.getConstant() ^ op2Value.getConstant());
                        else if (op1Value.isNAC() || op2Value.isNAC()) return Value.getNAC();
                        return Value.getUndef();
                    }
                }
            }
        }
        return Value.getNAC(); // other situations, like single invoke, m = o.f
    }
}
