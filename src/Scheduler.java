import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import IntermediateRepresentation.OpRecord;
import IntermediateRepresentation.Operand;
import Token.Opcode;

/**
 * Improved scheduler: builds a dependence graph, computes priorities (total latency),
 * and schedules using instruction latencies and two-issue constraints.
 * This is a simplified port of the reference scheduler behavior.
 */
public class Scheduler {
    private OpRecord head;

    public Scheduler(OpRecord head) {
        this.head = head;
    }

    private static class Node {
        OpRecord op;
        List<Node> outs = new ArrayList<>();
        List<Node> ins = new ArrayList<>();
        int latency = 1; // intrinsic latency
        int totalLatency = -1; // priority
        Status status = Status.NOT_READY;
        public Node(OpRecord op) { this.op = op; }
    }

    private enum Status { NOT_READY, READY, ACTIVE, RETIRED }

    public void printSchedule() {
        List<OpRecord> ops = collectOps();
        if (ops.isEmpty()) return;

        // build nodes and adjacency based on VR defs/uses (conservative)
        Map<OpRecord, Node> nodeOf = new HashMap<>();
        List<Node> nodes = new ArrayList<>();
        for (OpRecord op : ops) {
            Node n = new Node(op);
            n.latency = computeLatency(op.getOpCode());
            nodeOf.put(op, n);
            nodes.add(n);
        }

        // compute data edges (RAW/WAW/WAR) using VRs (or SRs if VR not available)
        List<Set<Integer>> defs = new ArrayList<>();
        List<Set<Integer>> uses = new ArrayList<>();
        for (OpRecord op : ops) {
            Set<Integer> d = new HashSet<>();
            Set<Integer> u = new HashSet<>();
            List<Operand> operands = op.getOperands();
            if (operands != null && operands.size() > 0) {
                Opcode opc = op.getOpCode();
                if (opc != Opcode.store) {
                    Operand def = operands.get(operands.size() - 1);
                    if (def != null && def.isRegister()) {
                        int reg = def.getVR() != -1 ? def.getVR() : def.getSR();
                        d.add(reg);
                    }
                }
                int upto = operands.size();
                if (opc != Opcode.store && operands.size() > 0) upto = operands.size() - 1;
                for (int i = 0; i < upto; i++) {
                    Operand use = operands.get(i);
                    if (use != null && use.isRegister()) {
                        int reg = use.getVR() != -1 ? use.getVR() : use.getSR();
                        u.add(reg);
                    }
                }
            }
            defs.add(d); uses.add(u);
        }

        int n = ops.size();
        for (int i = 0; i < n; i++) {
            nodeOf.get(ops.get(i));
        }

        // Create dependency edges
        for (int j = 0; j < n; j++) {
            for (int i = j + 1; i < n; i++) {
                boolean dep = false;
                Set<Integer> defj = defs.get(j);
                Set<Integer> usei = uses.get(i);

                // RAW (Read-After-Write): j defines a register that i uses
                for (Integer d : defj) {
                    if (usei.contains(d)) {
                        dep = true;
                        break;
                    }
                }

                // Note: We skip WAW and WAR dependencies when using SRs (unrenamed code)
                // because in-order issue automatically handles them
                if (!dep) {
                    // memory dependence handling: be conservative for stores, but allow
                    // load-load reordering when there is no intervening store.
                    Opcode opj = ops.get(j).getOpCode();
                    Opcode opi = ops.get(i).getOpCode();
                    if (opj == Opcode.load && opi == Opcode.load) {
                        // if no store occurs between j and i, allow reordering of loads
                        boolean storeBetween = false;
                        for (int k = j+1; k < i; k++) {
                            Opcode ok = ops.get(k).getOpCode();
                            if (ok == Opcode.store) { storeBetween = true; break; }
                        }
                        if (storeBetween) dep = true; // conservative if a store exists in between
                    } else if (opj == Opcode.load || opj == Opcode.store || opi == Opcode.load || opi == Opcode.store) {
                        // For pairs involving a store, require serialization unless both addresses are constant and different
                        Integer addrJ = getMemoryAddressConstant(ops.get(j));
                        Integer addrI = getMemoryAddressConstant(ops.get(i));
                        if (addrJ != null && addrI != null && !addrJ.equals(addrI)) {
                            // different constant addresses -> no dependency
                            dep = false;
                        } else {
                            dep = true;
                        }
                    }
                }
                if (dep) {
                    // Standard forward edges: j (earlier) -> i (later)
                    // ins = predecessors that must complete first
                    // outs = successors that depend on this
                    Node earlier = nodeOf.get(ops.get(j));
                    Node later = nodeOf.get(ops.get(i));
                    earlier.outs.add(later);  // earlier's successors
                    later.ins.add(earlier);   // later's predecessors
                }
            }
        }

        // compute priorities (totalLatency) via DFS
        for (Node nd : nodes) {
            if (nd.totalLatency == -1) computeTotalLatency(nd);
        }

        // ready heap: max-heap by totalLatency, tiebreak by original index (stable)
        PriorityQueue<NodeWithIndex> ready = new PriorityQueue<>((a,b) -> {
            int c = Integer.compare(b.node.totalLatency, a.node.totalLatency);
            if (c != 0) return c;
            return Integer.compare(a.idx, b.idx);
        });
        // Initial ready set: operations with no predecessors (ins empty)
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).ins.isEmpty()) {
                nodes.get(i).status = Status.READY;
                ready.offer(new NodeWithIndex(nodes.get(i), i));
            }
        }

        // mapping node -> original index for stable tie-breaks
        Map<Node, Integer> nodeIndex = new HashMap<>();
        for (int i = 0; i < nodes.size(); i++) nodeIndex.put(nodes.get(i), i);

        List<String> outLines = new ArrayList<>();
        int cycle = 1;
        Map<Integer, List<Node>> active = new HashMap<>(); // removalCycle -> nodes
        int scheduledCount = 0;

        while (!ready.isEmpty() || !active.isEmpty()) {
            // retire nodes whose removal cycle == cycle
            List<Node> retiring = active.getOrDefault(cycle, new ArrayList<>());
            for (Node rn : retiring) {
                rn.status = Status.RETIRED;
                scheduledCount++;
            }
            if (active.containsKey(cycle)) active.remove(cycle);

            // Check if operations that depend on retired ops can become ready
            for (Node retired : retiring) {
                for (Node successor : retired.outs) {
                    if (successor.status != Status.NOT_READY) continue;

                    // Check if ALL of successor's predecessors (ins) are retired
                    boolean allPredecessorsRetired = true;
                    for (Node pred : successor.ins) {
                        if (pred.status != Status.RETIRED) {
                            allPredecessorsRetired = false;
                            break;
                        }
                    }

                    if (allPredecessorsRetired) {
                        successor.status = Status.READY;
                        ready.offer(new NodeWithIndex(successor, nodeIndex.get(successor)));
                    }
                }
            }

            // schedule up to two ops this cycle
            Node slot1 = null, slot2 = null;
            List<NodeWithIndex> skipped = new ArrayList<>();

            while (!ready.isEmpty() && (slot1 == null || slot2 == null)) {
                NodeWithIndex nw = ready.poll();
                Node node = nw.node;
                Opcode opc = node.op.getOpCode();

                boolean placed = false;

                // Check if we can place this operation given what's already scheduled
                // Slot 1 (f1): memory ops (load/store) or any op
                // Slot 2 (f2): mult or non-memory ALU ops (add, sub, shift, loadI)
                if (opc == Opcode.output) {
                    // Output takes the entire cycle - can only be in slot1, blocks both slots
                    if (slot1 == null && slot2 == null) {
                        slot1 = node;
                        placed = true;
                    }
                } else if (opc == Opcode.load || opc == Opcode.store) {
                    // Memory ops can ONLY go in slot1
                    if (slot1 == null) {
                        slot1 = node;
                        placed = true;
                    }
                } else if (opc == Opcode.mult) {
                    // Mult can ONLY go in slot2
                    if (slot2 == null) {
                        slot2 = node;
                        placed = true;
                    }
                } else {
                    // Regular ALU ops (add, sub, shift, loadI)
                    // Can go in either slot - try slot2 first, then slot1
                    if (slot2 == null) {
                        slot2 = node;
                        placed = true;
                    } else if (slot1 == null) {
                        slot1 = node;
                        placed = true;
                    }
                }

                if (placed) {
                    // place node: add to active list to be retired after latency
                    int removeCycle = cycle + node.latency;
                    active.computeIfAbsent(removeCycle, k -> new ArrayList<>()).add(node);
                    node.status = Status.ACTIVE;
                } else {
                    skipped.add(nw);
                }
            }

            // push skipped back
            for (NodeWithIndex s : skipped) ready.offer(s);

            String s1 = slot1 == null ? "nop" : formatOp(slot1.op);
            String s2 = slot2 == null ? "nop" : formatOp(slot2.op);
            outLines.add(String.format("[ %s ; %s ]", s1, s2));

            cycle++;
            // safety: avoid infinite loop
            if (cycle > 100000) break;
        }

        for (String l : outLines) System.out.println(l);
    }

    private int computeTotalLatency(Node n) {
        if (n.totalLatency != -1) return n.totalLatency;
        int maxChild = 0;
        for (Node c : n.outs) {
            int v = computeTotalLatency(c);
            if (v > maxChild) maxChild = v;
        }
        n.totalLatency = n.latency + maxChild;
        return n.totalLatency;
    }

    private int computeLatency(Opcode op) {
        switch (op) {
            case load: case store: return 6;
            case mult: return 3;
            case add: case sub: case lshift: case rshift: case loadI: case output: case nop: default: return 1;
        }
    }

    private Integer getMemoryAddressConstant(OpRecord op) {
        // return SR if the memory address operand is a constant (load: operand1.SR, store: operand3.SR)
        if (op == null) return null;
        Opcode opc = op.getOpCode();
        if (opc == Opcode.load) {
            Operand a1 = op.getOperand1();
            if (a1 != null) return a1.getSR();
        } else if (opc == Opcode.store) {
            Operand a3 = op.getOperand3();
            if (a3 != null) return a3.getSR();
        }
        return null;
    }

    private List<OpRecord> collectOps() {
        List<OpRecord> ops = new ArrayList<>();
        OpRecord cur = this.head;
        while (cur != null) {
            ops.add(cur);
            cur = cur.getNext();
        }
        return ops;
    }

    private String formatOp(OpRecord curOp) {
        Opcode opCode = curOp.getOpCode();
        Integer operand1Register = null;
        Integer operand1Constant = null;
        Integer operand2Register = null;
        Integer operand3Register = null;
        if (curOp.getOperand1() != null) {
            operand1Register = curOp.getOperand1().getVR();
            operand1Constant = curOp.getOperand1().getSR();
        }
        if (curOp.getOperand2() != null) {
            operand2Register = curOp.getOperand2().getVR();
        }
        if (curOp.getOperand3() != null) {
            operand3Register = curOp.getOperand3().getVR();
        }

        switch (opCode) {
            case load:
                return String.format("%s r%d => r%d", opCode, operand1Register, operand3Register);
            case loadI:
                return String.format("%s %d => r%d", opCode, operand1Constant, operand3Register);
            case store:
                return String.format("%s r%d => r%d", opCode, operand1Register, operand3Register);
            case add: case sub: case mult: case lshift: case rshift:
                return String.format("%s r%d, r%d => r%d", opCode, operand1Register, operand2Register, operand3Register);
            case output:
                return String.format("%s %d", opCode, operand1Constant);
            case nop:
                return "nop";
            default:
                return opCode.toString();
        }
    }

    private static class NodeWithIndex {
        Node node; int idx; NodeWithIndex(Node n, int i){ node=n; idx=i; }
    }
}
