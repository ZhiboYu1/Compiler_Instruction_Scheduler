import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import IntermediateRepresentation.OpRecord;
import IntermediateRepresentation.Operand;
import Token.Opcode;

/**
 * Conservative two-issue scheduler.
 *
 * This scheduler builds a conservative dependence graph using VR defs/uses and
 * treats memory ops (loads/stores) as serializing with other memory ops.
 * It then issues up to two operations per cycle with simple slot constraints:
 *  - Slot1 (operationOne): load/store preferred here; also other ops if available
 *  - Slot2 (operationTwo): mult only here; other ops allowed if slot2 free
 *  - output: only one per cycle (placed in slot1)
 *
 * NOTE: This is a conservative/simple scheduler meant to provide reasonable
 * instruction reordering for the lab. It does not implement full address
 * dependence reasoning or latency-based prioritization from the reference
 * implementation.
 */
public class Scheduler {
    private OpRecord head; // first real OpRecord (not the sentinel head)

    public Scheduler(OpRecord head) {
        this.head = head;
    }

    public void printSchedule() {
        List<OpRecord> ops = collectOps();
        if (ops.size() == 0) return;

        Map<OpRecord, List<OpRecord>> adj = buildDeps(ops);
        Map<OpRecord, Integer> indeg = new HashMap<>();
        for (OpRecord op : ops) indeg.put(op, 0);
        for (OpRecord u : adj.keySet()) {
            for (OpRecord v : adj.get(u)) {
                indeg.put(v, indeg.get(v) + 1);
            }
        }

        // ready queue: preserve original order by using the op's index (position)
        PriorityQueue<OpWithIndex> ready = new PriorityQueue<>((a,b) -> Integer.compare(a.idx, b.idx));
        for (int i = 0; i < ops.size(); i++) {
            OpRecord op = ops.get(i);
            if (indeg.get(op) == 0) ready.offer(new OpWithIndex(op, i));
        }

        List<String> scheduleLines = new ArrayList<>();
        int scheduledCount = 0;
        // simple scheduler loop
        while (!ready.isEmpty() || scheduledCount < ops.size()) {
            // build a cycle block (two slots)
            OpRecord slot1 = null;
            OpRecord slot2 = null;

            List<OpWithIndex> skipped = new ArrayList<>();

            int issued = 0;
            while (issued < 2 && !ready.isEmpty()) {
                OpWithIndex ow = ready.poll();
                OpRecord op = ow.op;
                String opcode = op.getOpCode().toString();

                boolean placed = false;
                switch (opcode) {
                    case "output":
                        if (slot1 == null) {
                            slot1 = op; placed = true; issued = 2; // output consumes the cycle
                        } else {
                            skipped.add(ow);
                        }
                        break;
                    case "mult":
                        if (slot2 == null) { slot2 = op; placed = true; issued++; }
                        else { skipped.add(ow); }
                        break;
                    case "load":
                    case "store":
                        if (slot1 == null) { slot1 = op; placed = true; issued++; }
                        else { skipped.add(ow); }
                        break;
                    default:
                        // any-other op can go in slot2 if free, otherwise slot1
                        if (slot2 == null) { slot2 = op; placed = true; issued++; }
                        else if (slot1 == null) { slot1 = op; placed = true; issued++; }
                        else { skipped.add(ow); }
                        break;
                }

                if (!placed) continue;
            }

            // format line
            String op1s = slot1 == null ? "nop" : formatOp(slot1);
            String op2s = slot2 == null ? "nop" : formatOp(slot2);
            scheduleLines.add(String.format("[ %s ; %s ]", op1s, op2s));

            // mark scheduled and update indegrees
            List<OpRecord> justScheduled = new ArrayList<>();
            if (slot1 != null) { justScheduled.add(slot1); scheduledCount++; }
            if (slot2 != null && slot2 != slot1) { justScheduled.add(slot2); scheduledCount++; }

            for (OpRecord s : justScheduled) {
                List<OpRecord> neighbors = adj.getOrDefault(s, new ArrayList<>());
                for (OpRecord v : neighbors) {
                    indeg.put(v, indeg.get(v) - 1);
                    if (indeg.get(v) == 0) {
                        // push with its original index
                        int idx = ops.indexOf(v);
                        ready.offer(new OpWithIndex(v, idx));
                    }
                }
            }

            // push skipped back to ready
            for (OpWithIndex w : skipped) ready.offer(w);

            // safety: if nothing scheduled but ready not empty (due to placement constraints), force one
            if (justScheduled.size() == 0 && !ready.isEmpty()) {
                OpWithIndex forced = ready.poll();
                OpRecord fop = forced.op;
                scheduleLines.add(String.format("[ %s ; %s ]", formatOp(fop), "nop"));
                scheduledCount++;
                List<OpRecord> neighbors = adj.getOrDefault(fop, new ArrayList<>());
                for (OpRecord v : neighbors) {
                    indeg.put(v, indeg.get(v) - 1);
                    if (indeg.get(v) == 0) ready.offer(new OpWithIndex(v, ops.indexOf(v)));
                }
            }
        }

        // print schedule
        for (String line : scheduleLines) System.out.println(line);
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

    private Map<OpRecord, List<OpRecord>> buildDeps(List<OpRecord> ops) {
        Map<OpRecord, List<OpRecord>> adj = new HashMap<>();
        int n = ops.size();
        // precompute defs and uses (VRs)
        List<Set<Integer>> defs = new ArrayList<>();
        List<Set<Integer>> uses = new ArrayList<>();
        for (OpRecord op : ops) {
            Set<Integer> d = new HashSet<>();
            Set<Integer> u = new HashSet<>();
            List<Operand> operands = op.getOperands();
            if (operands != null && operands.size() > 0) {
                // last operand (unless store) is defining register
                Opcode opc = op.getOpCode();
                if (opc != Opcode.store) {
                    Operand def = operands.get(operands.size() - 1);
                    if (def != null && def.isRegister()) d.add(def.getVR());
                }
                // uses are the remaining operands
                int upto = operands.size();
                if (opc != Opcode.store && operands.size() > 0) upto = operands.size() - 1;
                for (int i = 0; i < upto; i++) {
                    Operand use = operands.get(i);
                    if (use != null && use.isRegister()) u.add(use.getVR());
                }
            }
            defs.add(d); uses.add(u);
        }

        // conservative memory handling: treat any load/store as serializing with other loads/stores
        for (int i = 0; i < n; i++) adj.put(ops.get(i), new ArrayList<>());
        for (int j = 0; j < n; j++) {
            for (int i = j+1; i < n; i++) {
                boolean dependent = false;
                // RAW/WAR/WAW: check defs[j] vs uses[i] or defs[i]
                Set<Integer> defj = defs.get(j);
                Set<Integer> usei = uses.get(i);
                Set<Integer> defi = defs.get(i);
                // RAW
                for (Integer d : defj) if (usei.contains(d)) { dependent = true; break; }
                if (!dependent) {
                    // WAR or WAW
                    for (Integer d : defi) if (defj.contains(d)) { dependent = true; break; }
                }

                // conservative memory dependence: if either is load/store, serialize
                Opcode opj = ops.get(j).getOpCode();
                Opcode opi = ops.get(i).getOpCode();
                if (!dependent) {
                    if (opj == Opcode.load || opj == Opcode.store || opi == Opcode.load || opi == Opcode.store) {
                        dependent = true;
                    }
                }

                if (dependent) {
                    adj.get(ops.get(j)).add(ops.get(i));
                }
            }
        }

        return adj;
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

    private static class OpWithIndex {
        public OpRecord op;
        public int idx;
        public OpWithIndex(OpRecord o, int i) { this.op = o; this.idx = i; }
    }
}
