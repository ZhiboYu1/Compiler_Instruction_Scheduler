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

    private enum EdgeType { FLOW, CONFLICT, SERIALIZATION }

    private static class Edge {
        Node target;
        EdgeType type;
        Edge(Node target, EdgeType type) {
            this.target = target;
            this.type = type;
        }
    }

    private static class Node {
        OpRecord op;
        List<Edge> outs = new ArrayList<>();  // edges TO successors
        List<Edge> ins = new ArrayList<>();   // edges FROM predecessors
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

        // Track the LAST definition of each register (for more precise dependencies)
        Map<Integer, Integer> lastDef = new HashMap<>(); // register -> operation index

        // Create dependency edges
        for (int i = 0; i < n; i++) {
            Node curNode = nodeOf.get(ops.get(i));
            Set<Integer> curUses = uses.get(i);
            Set<Integer> curDefs = defs.get(i);

            // RAW: For each register this operation uses, depend on its last definition
            for (Integer reg : curUses) {
                if (lastDef.containsKey(reg)) {
                    int defIdx = lastDef.get(reg);
                    Node defNode = nodeOf.get(ops.get(defIdx));
                    defNode.outs.add(new Edge(curNode, EdgeType.FLOW));
                    curNode.ins.add(new Edge(defNode, EdgeType.FLOW));
                }
            }

            // WAW: For each register this operation defines, depend on its previous definition
            for (Integer reg : curDefs) {
                if (lastDef.containsKey(reg)) {
                    int prevDefIdx = lastDef.get(reg);
                    Node prevDefNode = nodeOf.get(ops.get(prevDefIdx));
                    prevDefNode.outs.add(new Edge(curNode, EdgeType.FLOW));
                    curNode.ins.add(new Edge(prevDefNode, EdgeType.FLOW));
                }
                // Update last definition
                lastDef.put(reg, i);
            }
        }

        // Add memory dependencies based on Lab3 DG Script Slide 16 table
        for (int j = 0; j < n; j++) {
            Opcode opj = ops.get(j).getOpCode();
            if (opj != Opcode.load && opj != Opcode.store && opj != Opcode.output) continue;

            for (int i = j + 1; i < n; i++) {
                Opcode opi = ops.get(i).getOpCode();
                if (opi != Opcode.load && opi != Opcode.store && opi != Opcode.output) continue;

                EdgeType edgeType = null;
                boolean createEdge = false;

                // Check if addresses are provably different
                Integer addrJ = getMemoryAddressConstant(ops.get(j));
                Integer addrI = getMemoryAddressConstant(ops.get(i));
                boolean samAddr = (addrJ != null && addrI != null && addrJ.equals(addrI));
                boolean diffAddr = (addrJ != null && addrI != null && !addrJ.equals(addrI));

                // Apply the dependency table from DG Script Slide 16
                if (opj == Opcode.load && opi == Opcode.load) {
                    // Load → Load: independent in all cases
                    createEdge = false;
                } else if (opj == Opcode.load && opi == Opcode.store) {
                    // Load → Store: SERIALIZATION (WAR) unless different addresses
                    if (!diffAddr) {
                        createEdge = true;
                        edgeType = EdgeType.SERIALIZATION;
                    }
                } else if (opj == Opcode.load && opi == Opcode.output) {
                    // Load → Output: independent
                    createEdge = false;
                } else if (opj == Opcode.store && opi == Opcode.load) {
                    // Store → Load: CONFLICT (RAW) unless different addresses
                    if (!diffAddr) {
                        createEdge = true;
                        edgeType = EdgeType.CONFLICT;
                    }
                } else if (opj == Opcode.store && opi == Opcode.store) {
                    // Store → Store: SERIALIZATION (WAW) unless different addresses
                    if (!diffAddr) {
                        createEdge = true;
                        edgeType = EdgeType.SERIALIZATION;
                    }
                } else if (opj == Opcode.store && opi == Opcode.output) {
                    // Store → Output: CONFLICT (RAW) unless different addresses
                    if (!diffAddr) {
                        createEdge = true;
                        edgeType = EdgeType.CONFLICT;
                    }
                } else if (opj == Opcode.output && opi == Opcode.load) {
                    // Output → Load: independent
                    createEdge = false;
                } else if (opj == Opcode.output && opi == Opcode.store) {
                    // Output → Store: SERIALIZATION (WAR) always
                    createEdge = true;
                    edgeType = EdgeType.SERIALIZATION;
                } else if (opj == Opcode.output && opi == Opcode.output) {
                    // Output → Output: SERIALIZATION (WAW) always
                    createEdge = true;
                    edgeType = EdgeType.SERIALIZATION;
                }

                if (createEdge) {
                    Node earlier = nodeOf.get(ops.get(j));
                    Node later = nodeOf.get(ops.get(i));
                    earlier.outs.add(new Edge(later, edgeType));
                    later.ins.add(new Edge(earlier, edgeType));
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
                for (Edge outEdge : retired.outs) {
                    Node successor = outEdge.target;
                    if (successor.status != Status.NOT_READY) continue;

                    // Check if ALL of successor's predecessors are satisfied
                    // FLOW and CONFLICT edges: wait for RETIRED
                    // SERIALIZATION edges: satisfied when operation issues (1 cycle)
                    boolean allDependenciesSatisfied = true;
                    for (Edge inEdge : successor.ins) {
                        Node pred = inEdge.target;
                        if (pred.status == Status.NOT_READY) {
                            allDependenciesSatisfied = false;
                            break;
                        }
                        // For FLOW and CONFLICT edges, must wait for RETIRED
                        if ((inEdge.type == EdgeType.FLOW || inEdge.type == EdgeType.CONFLICT) &&
                            pred.status != Status.RETIRED) {
                            allDependenciesSatisfied = false;
                            break;
                        }
                        // For SERIALIZATION edges, ACTIVE or RETIRED is sufficient (early release)
                    }

                    if (allDependenciesSatisfied) {
                        successor.status = Status.READY;
                        ready.offer(new NodeWithIndex(successor, nodeIndex.get(successor)));
                    }
                }
            }

            // EARLY RELEASE: Check for operations with serialization dependencies on ACTIVE operations
            // This implements Step 4 from the scheduling algorithm
            for (List<Node> activeOps : active.values()) {
                for (Node activeNode : activeOps) {
                    // Only memory ops can have serial successors
                    Opcode opc = activeNode.op.getOpCode();
                    if (opc != Opcode.load && opc != Opcode.store && opc != Opcode.output) continue;

                    for (Edge outEdge : activeNode.outs) {
                        if (outEdge.type != EdgeType.SERIALIZATION) continue;

                        Node successor = outEdge.target;
                        if (successor.status != Status.NOT_READY) continue;

                        // Check if ALL other dependencies are satisfied
                        boolean allOtherDependenciesSatisfied = true;
                        for (Edge inEdge : successor.ins) {
                            Node pred = inEdge.target;
                            if (pred == activeNode) continue; // Skip the serial edge we're releasing

                            if (pred.status == Status.NOT_READY) {
                                allOtherDependenciesSatisfied = false;
                                break;
                            }
                            if ((inEdge.type == EdgeType.FLOW || inEdge.type == EdgeType.CONFLICT) &&
                                pred.status != Status.RETIRED) {
                                allOtherDependenciesSatisfied = false;
                                break;
                            }
                        }

                        if (allOtherDependenciesSatisfied) {
                            successor.status = Status.READY;
                            ready.offer(new NodeWithIndex(successor, nodeIndex.get(successor)));
                        }
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
        for (Edge e : n.outs) {
            int v = computeTotalLatency(e.target);
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
