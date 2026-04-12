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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        HashSet<JMethod> reachingMethod = new HashSet<>();
        List<JMethod> worklist = new ArrayList<>();
        DefaultCallGraph callGraph = new DefaultCallGraph();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod m = worklist.remove(0);
            if (!reachingMethod.contains(m)) {
                reachingMethod.add(m);
                m.getIR().getStmts().stream()
                        .filter(stmt -> stmt instanceof Invoke)
                        .map(stmt -> (Invoke) stmt)
                        .forEach(invoke -> {
                            resolve(invoke).forEach(method -> {
                                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method));
                                worklist.add(method);
                            });
                        });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> t = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        if (callSite.isStatic()) {
            t.add(methodRef.resolve());
        }
        if (callSite.isSpecial()) {
            JMethod dispatch = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
            if (dispatch != null) {
                t.add(dispatch);
            }
        }
        if (callSite.isVirtual()) {
            JClass declaringClass = methodRef.getDeclaringClass();
            Queue<JClass> queue = new ArrayDeque<>();
            queue.add(declaringClass);
            while (!queue.isEmpty()) {
                JClass c = queue.poll();
                JMethod m = dispatch(c, methodRef.getSubsignature());
                if (m != null) {
                    t.add(m);
                }
                queue.addAll(hierarchy.getDirectSubclassesOf(c));
            }
        }
        return t;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        if (declaredMethod != null) {
            return declaredMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass == null) {
            return null;
        }
        return dispatch(superClass, subsignature);
    }
}
