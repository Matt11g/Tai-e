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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.Queue;
import java.util.LinkedList;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<Node>();
        for (Node node : cfg) workList.add(node);
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            //Fact temp = result.getOutFact(node);
            result.setInFact(node, analysis.newInitialFact()); // 总感觉要清空？？
            for (Node pre : cfg.getPredsOf(node)) {
                analysis.meetInto(result.getOutFact(pre), result.getInFact(node));
            }
            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) { //FixBug: 修改用伪代码中用temp判断，WHY??
                //workList.addAll(cfg.getSuccsOf(node)); // 没去重的写法，不过感觉没有问题
                for (Node success : cfg.getSuccsOf(node)) {
                    if (!workList.contains(success)) workList.add(success);
                }
            }
            //  还是 if (transferNode()) workList.add(..);  ??
        }
//        boolean isChange = true;
//        while (isChange) {
//            isChange = false;
//            for (Node node : cfg) {
//                if (cfg.isEntry(node)) continue;
//                for (Node pre : cfg.getPredsOf(node)) {
//                    analysis.meetInto(result.getOutFact(pre), result.getInFact(node));
//                }
//                if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
//                    isChange = true; // changes to any OUT occurs
//                }
//            }
//        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
