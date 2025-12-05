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

        // compute data edges (RAW/WAW/WAR) using VRs
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
                    if (def != null && def.isRegister()) d.add(def.getVR());
                }
                int upto = operands.size();
                if (opc != Opcode.store && operands.size() > 0) upto = operands.size() - 1;
                for (int i = 0; i < upto; i++) {
                    Operand use = operands.get(i);
                    if (use != null && use.isRegister()) u.add(use.getVR());
                }
            }
            defs.add(d); uses.add(u);
        }

        int n = ops.size();
        for (int i = 0; i < n; i++) {
            nodeOf.get(ops.get(i));
        }

        // create edges from earlier to later when dependency detected
        for (int j = 0; j < n; j++) {
            for (int i = j + 1; i < n; i++) {
                boolean dep = false;
                Set<Integer> defj = defs.get(j);
                Set<Integer> usei = uses.get(i);
                Set<Integer> defi = defs.get(i);
                for (Integer d : defj) if (usei.contains(d)) { dep = true; break; }
                if (!dep) {
                    for (Integer d : defi) if (defj.contains(d)) { dep = true; break; }
                }
                if (!dep) {
                    // conservative memory serialization for correctness
                    Opcode opj = ops.get(j).getOpCode();
                    Opcode opi = ops.get(i).getOpCode();
                    if (opj == Opcode.load || opj == Opcode.store || opi == Opcode.load || opi == Opcode.store) dep = true;
                }
                if (dep) {
                    Node a = nodeOf.get(ops.get(j));
                    Node b = nodeOf.get(ops.get(i));
                    a.outs.add(b);
                    b.ins.add(a);
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
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).ins.isEmpty()) {
                nodes.get(i).status = Status.READY;
                ready.offer(new NodeWithIndex(nodes.get(i), i));
            }
        }

        List<String> outLines = new ArrayList<>();
        int cycle = 1;
        Map<Integer, List<Node>> active = new HashMap<>(); // removalCycle -> nodes
        int busy1Until = 0, busy2Until = 0;
        int scheduledCount = 0;

        while (!ready.isEmpty() || !active.isEmpty()) {
            // retire nodes whose removal cycle == cycle
            List<Node> retiring = active.getOrDefault(cycle, new ArrayList<>());
            for (Node rn : retiring) {
                rn.status = Status.RETIRED;
                scheduledCount++;
            }
            if (active.containsKey(cycle)) active.remove(cycle);

            // add newly-ready nodes whose predecessors retired
            for (Node nd : nodes) {
                if (nd.status == Status.NOT_READY) {
                    boolean readyAll = true;
                    for (Node p : nd.ins) if (p.status != Status.RETIRED) { readyAll = false; break; }
                    if (readyAll) { nd.status = Status.READY; ready.offer(new NodeWithIndex(nd, nodes.indexOf(nd))); }
                }
            }

            // schedule up to two ops this cycle respecting resource busy-until
            Node slot1 = null, slot2 = null;
            List<NodeWithIndex> skipped = new ArrayList<>();

            while (ready.size() > 0 && (slot1 == null || slot2 == null)) {
                NodeWithIndex nw = ready.poll();
                Node node = nw.node;
                Opcode opc = node.op.getOpCode();
                int nodeLatency = node.latency;

                boolean placed = false;
                if (opc == Opcode.output) {
                    if (slot1 == null && busy1Until <= cycle) { slot1 = node; placed = true; }
                } else if (opc == Opcode.mult) {
                    if (slot2 == null && busy2Until <= cycle) { slot2 = node; placed = true; }
                } else if (opc == Opcode.load || opc == Opcode.store) {
                    if (slot1 == null && busy1Until <= cycle) { slot1 = node; placed = true; }
                } else {
                    // other ops prefer slot2
                    if (slot2 == null && busy2Until <= cycle) { slot2 = node; placed = true; }
                    else if (slot1 == null && busy1Until <= cycle) { slot1 = node; placed = true; }
                }

                if (!placed) {
                    skipped.add(nw);
                    continue;
                }

                // place node: set busyUntil and add to active
                int removeCycle = cycle + nodeLatency;
                active.computeIfAbsent(removeCycle, k -> new ArrayList<>()).add(node);
                node.status = Status.ACTIVE;
                if (slot1 == node) busy1Until = removeCycle;
                if (slot2 == node) busy2Until = removeCycle;
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
