import java.io.File;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import IntermediateRepresentation.OpRecord;
import IntermediateRepresentation.Operand;
import Token.Token;
import Token.TokenCategory;
import Token.Opcode;

public class Parser {
    private OpRecord IRHead; //the head of the doubly linked list of internal representation records
    private OpRecord IRTail; //the tail of the doubly linked list
    private int maxSRNumber; 
    private int maxLive;
    private int maxVRNumber;
    private Scanner scanner;
    private int numOperationsParsed; //number of operations that have been parsed; will be returned at the end
    private List<Token> operationTokenLst; //a list of tokens that are part of the operations
    private boolean hasError;

    private int[] SRToVR; //SRToVR[i] represents the VR number corresponding to i
    private int[] LU; //LU[i] represents the code block line index that has the last usage of source register ri 
    // private int[] VRToPR;
    // private int[] PRToVR;
    // private int[] PRNU;
    // private Deque<Integer> PRStack;
    /**
     * 
     * @param toBeParsedFile
     */
    public Parser(File toBeParsedFile){
        this.scanner = new Scanner(toBeParsedFile);
        this.IRHead = new OpRecord(-1, null, null, null, null);
        this.maxSRNumber = 0;
        this.maxVRNumber = 0;
        this.maxLive = 0;
        this.operationTokenLst = new ArrayList<>();
        this.hasError = false;
    }

    public void parse(){
        this.hasError = false;
        Token nextToken;
        //set current node to be the head node
        OpRecord curOpIR = this.IRHead;
        OpRecord preOpIR = null;
        while ((nextToken = this.scanner.nextToken()) != null){

            // reset operationTokenLst to empty
            this.operationTokenLst = new ArrayList<>();
            // when nextToken is EOF, we end reading the next token
            if (nextToken.getTokenCategory().ordinal() == 9) break;

            // otherwise, we keep iterating on each operation
            // we find an operation by keep calling nextToken() until we reach a EOL token
            while (nextToken.getTokenCategory().ordinal() != 10) {
                this.operationTokenLst.add(nextToken);
                nextToken = this.scanner.nextToken();
            }
            // size 0 means we are reading an empty line or a comment
            if (this.operationTokenLst.size() == 0) {
                continue;
            }

            OpRecord newIR = createIR(this.operationTokenLst);

            // increment the number of operations parsed
            this.numOperationsParsed++;
            // scenario where the newIR is valid
            if (newIR != null) {
                this.IRTail = newIR;
                // set the next pointer of curOpIR, and set the prev pointer of newIR
                newIR.setPrev(curOpIR);
                curOpIR.setNext(newIR);
                // move the curOpIR to pre; move the newIR to cur 
                preOpIR = curOpIR;
                curOpIR = newIR;
            } else {
                // scenario where the newIR is invalid
                // TODO: how to report error from createIR method

                // print out error first 
                this.hasError = true;
            }
        }
        if (!this.hasError) {
            //System.out.println(String.format("Parse succeeded. Processed %d operations.", this.numOperationsParsed));
        } else {
            System.out.println("Parse found errors.");
        }
        
    }
    public void parseAndPrintIR(){
        //System.out.println("parse and print IR");
        parse();
        
        if (!hasError) {
            OpRecord cur = this.IRHead.getNext();
            while (cur != null) {
                System.out.println(cur.toString());
                cur = cur.getNext();
            }
        }

    }
    /**
     * This function is used for parse the original ILOC block, rename all register names, and print the renamed ILOC block
     */
    public void parseRenameAndPrintILOC(boolean printVR, boolean printPR, int k){
        parse();
        renameIR();
        //Register Allocation
        if (printPR) {
            RegisterAllocator registerAllocator = new RegisterAllocator(k, this.maxLive, this.IRHead.getNext(), this.maxVRNumber);
            registerAllocator.allocateRegister();
        }
        printRenamedIR(printVR, printPR);
    }
    /**
     * Helper function to build internal representation object from the list of tokens
     * @param operationTokenLst 
     * @return
     */
    private OpRecord createIR(List<Token> operationTokenLst){
        TokenCategory tokenCategory = operationTokenLst.get(0).getTokenCategory();

        switch (tokenCategory) {
            case MEMOP:
                return createMemopIR(operationTokenLst);
            case LOADI:
                return createLoadiIR(operationTokenLst);
            case ARITHOP:
                return createArithopIR(operationTokenLst);
            case OUTPUT:
                return createOutputIR(operationTokenLst);
            case NOP:
                return createNopIR(operationTokenLst);
            default:
                printErr(operationTokenLst.get(0), operationTokenLst.get(0));
                return null;
        }
    }
    
    private OpRecord createMemopIR(List<Token> operationTokenLst){
        Token shouldBeRegister1 = expectToken(operationTokenLst, 1, TokenCategory.REGISTER);
        if (shouldBeRegister1 == null) return null;

        Token shouldBeInto = expectToken(operationTokenLst, 2, TokenCategory.INTO);
        if (shouldBeInto == null) return null;

        Token shouldBeRegister2 = expectToken(operationTokenLst, 3, TokenCategory.REGISTER);
        if (shouldBeRegister2 == null) return null;

        Token operatorToken = operationTokenLst.get(0);
        int lineNum = operatorToken.getLineNumber();
        Opcode opCode = operatorToken.getOpCode();
        Operand operand1 = new Operand(convertLexemeToSR(shouldBeRegister1.getLexeme()), -1, -1, -1, true);
        Operand operand3 = new Operand(convertLexemeToSR(shouldBeRegister2.getLexeme()), -1, -1, -1, true);
        OpRecord opRecord = new OpRecord(lineNum, opCode, operand1, null, operand3);
        return opRecord;
    }
    private OpRecord createLoadiIR(List<Token> operationTokenLst){

        Token shouldBeConst = expectToken(operationTokenLst, 1, TokenCategory.CONSTANT);
        if (shouldBeConst == null) return null;

        Token shouldBeInto = expectToken(operationTokenLst, 2, TokenCategory.INTO);
        if (shouldBeInto == null) return null;

        Token shouldBeRegister = expectToken(operationTokenLst, 3, TokenCategory.REGISTER);
        if (shouldBeRegister == null) return null;

        Token operatorToken = operationTokenLst.get(0);
        int lineNum = operatorToken.getLineNumber();
        Opcode opCode = operatorToken.getOpCode();
        Operand operand1 = new Operand(convertLexemeToSR(shouldBeConst.getLexeme()), -1, -1, -1, false);
        Operand operand3 = new Operand(convertLexemeToSR(shouldBeRegister.getLexeme()), -1, -1, -1, true);
        OpRecord opRecord = new OpRecord(lineNum, opCode, operand1, null, operand3);
        return opRecord;
    }
    
    private OpRecord createArithopIR(List<Token> operationTokenLst){

        Token shouldBeRegister1 = expectToken(operationTokenLst, 1, TokenCategory.REGISTER);
        if (shouldBeRegister1 == null) return null;
        
        Token shouldBeComma = expectToken(operationTokenLst, 2, TokenCategory.COMMA);
        if (shouldBeComma == null) return null;

        Token shouldBeRegister2 = expectToken(operationTokenLst, 3, TokenCategory.REGISTER);
        if (shouldBeRegister2 == null) return null;

        Token shouldBeInto = expectToken(operationTokenLst, 4, TokenCategory.INTO);
        if (shouldBeInto == null) return null;

        Token shouldBeRegister3 = expectToken(operationTokenLst, 5, TokenCategory.REGISTER);
        if (shouldBeRegister3 == null) return null;
             
        Token operatorToken = operationTokenLst.get(0);
        int lineNum = operatorToken.getLineNumber();
        Opcode opCode = operatorToken.getOpCode();
        Operand operand1 = new Operand(convertLexemeToSR(shouldBeRegister1.getLexeme()), -1, -1, -1, true);
        Operand operand2 = new Operand(convertLexemeToSR(shouldBeRegister2.getLexeme()), -1, -1, -1, true);
        Operand operand3 = new Operand(convertLexemeToSR(shouldBeRegister3.getLexeme()), -1, -1, -1, true);
        OpRecord opRecord = new OpRecord(lineNum, opCode, operand1, operand2, operand3);
        return opRecord;
    }
    private OpRecord createOutputIR(List<Token> operationTokenLst){

        Token shouldBeConstant = expectToken(operationTokenLst, 1, TokenCategory.CONSTANT);
        if (shouldBeConstant == null) return null;

        Token operatorToken = operationTokenLst.get(0);
        int lineNum = operatorToken.getLineNumber();
        Opcode opCode = operatorToken.getOpCode();
        Operand operand1 = new Operand(convertLexemeToSR(shouldBeConstant.getLexeme()), -1, -1, -1, false);  

        OpRecord opRecord = new OpRecord(lineNum, opCode, operand1, null, null);
        return opRecord;
    }
    private OpRecord createNopIR(List<Token> operationTokenLst){
        
        Token operatorToken = operationTokenLst.get(0);
        if (operationTokenLst.size() != 1) {
            System.err.println(String.format("ERROR %d: \tnop operation is not supposed to have any tokens", operatorToken.getLineNumber()));
        }
        int lineNum = operatorToken.getLineNumber();
        Opcode opCode = operatorToken.getOpCode();
        OpRecord opRecord = new OpRecord(lineNum, opCode, null, null, null);
        return opRecord;
    }
    private Token expectToken(List<Token> tokens, int index, TokenCategory expectedCategory) {
        Token tok = (index >= 0 && index < tokens.size()) ? tokens.get(index) : null;
        if (tok == null || tok.getTokenCategory() != expectedCategory) {
            printErr(tokens.get(0), tok);
            return null;
        }
        return tok;
    }
    /**
     * This helper method is used to convert register lexeme into an integer of its source register
     * In other words, turn "r128" into 128 (integer)
     * If the input lexeme is already an integer, then we simply convert it into Integer
     */
    private Integer convertLexemeToSR(String lexeme){
        Integer srNumber = null;
        try {
            if (lexeme.charAt(0) == 'r') {
                srNumber = Integer.valueOf(lexeme.substring(1));
                if (srNumber > this.maxSRNumber) this.maxSRNumber = srNumber;
                return srNumber;
            } else {
                return Integer.valueOf(lexeme);
            }
        } catch (NumberFormatException e) {
             System.err.println("Invalid string format for integer conversion: " + e.getMessage());
             return srNumber;
        }
    }
    private void printErr(Token operationToken, Token curToken){
        if (curToken == null) {
            System.err.println(String.format("ERROR %d: \tMissing Token", operationToken.getLineNumber()));
            return;
        }
        System.err.println(String.format("ERROR %d: \t\"%s\" is not a valid word.", operationToken.getLineNumber(), curToken.getLexeme()));
    }
    
    private void renameIR() {
        int VRName = 0;
        this.SRToVR = new int[this.maxSRNumber + 1];
        this.LU = new int[this.maxSRNumber + 1];
        for (int i = 0; i <= this.maxSRNumber; i++) {
            this.SRToVR[i] = -1;//invalid value
            LU[i] = Integer.MAX_VALUE;
        }
        int index = this.IRTail.getLine();

        OpRecord curOpRecord = this.IRTail;

        //loop through all operations from bottom to top
        while (!curOpRecord.equals(this.IRHead)){
            //System.out.println("curOpRecord: " + curOpRecord.toString());
            List<Operand> curRecordOperands = curOpRecord.getOperands();
            
            if (curRecordOperands == null) {
                curOpRecord = curOpRecord.getPrev();
                //System.out.println("curOpRecord: "+ curOpRecord.toString());
                continue;
            }

            int operandsSize = curRecordOperands.size();
            // edge case when the current record is EOF
            if (operandsSize == 0) {
                curOpRecord = curOpRecord.getPrev();
                //System.out.println("curOpRecord: "+ curOpRecord.toString());
                continue;
            }
            //handle defined register first 
            Operand definedRegister = curRecordOperands.get(operandsSize - 1);
            if (curOpRecord.getOpCode() != Opcode.store){
                if (!definedRegister.isRegister()) {
                    curOpRecord = curOpRecord.getPrev();
                    //System.out.println("curOpRecord: "+ curOpRecord.toString());
                    continue;
                }//it means that the current operation is OUTPUT, and the only operand is an integer

                if (this.SRToVR[definedRegister.getSR()] == -1) { // unused DEF
                    this.SRToVR[definedRegister.getSR()] = VRName++;
                    this.maxVRNumber++;
                }
                definedRegister.setVR(this.SRToVR[definedRegister.getSR()]);
                //System.out.println(String.format("the vr for sr [r%d] is: r%d", definedRegister.getSR(), definedRegister.getVR()));
                definedRegister.setNU(LU[definedRegister.getSR()]);
                this.SRToVR[definedRegister.getSR()] = -1;//kill OP3
                this.LU[definedRegister.getSR()] = Integer.MAX_VALUE;
            }
            

            // Now handle used registers
            if (curOpRecord.getOpCode() != Opcode.store){
                curRecordOperands.remove(operandsSize - 1);
            }
            // System.out.println("currentRecordOperands: " + curRecordOperands);
            // System.out.println("currentRecordOp size: " + curRecordOperands.size());
            for (Operand usedOperand : curRecordOperands){
                if (!usedOperand.isRegister()) {
                    continue; 
                }//skip non-register operands
                //System.out.println("current VR: " + this.SRToVR[usedOperand.getSR()]);
                if (this.SRToVR[usedOperand.getSR()] == -1){
                    //System.out.println(String.format("current SR: r%d; current VR: r%d", usedOperand.getSR(), usedOperand.getVR()));
                    this.SRToVR[usedOperand.getSR()] = VRName++;
                }
                
                usedOperand.setVR(this.SRToVR[usedOperand.getSR()]);
                //System.out.println(String.format("after setting VR, current SR: r%d; current VR: r%d", usedOperand.getSR(), usedOperand.getVR()));
                //System.out.println(String.format("the vr for sr [r%d] is: r%d", definedRegister.getSR(), definedRegister.getVR()));
                usedOperand.setNU(LU[usedOperand.getSR()]);
            }
            for (Operand op : curRecordOperands){
                if (!op.isRegister()) continue; //skip non-register operands
                this.LU[op.getSR()] = index;
            }
            index--;
            // update maxLive
            int curLive = 0;
            for (int val : this.SRToVR) {
                if (val != -1) curLive++;
            }
            if (curLive > this.maxLive) this.maxLive = curLive;
            
            curOpRecord = curOpRecord.getPrev();
            
        }
        this.maxVRNumber = VRName - 1;
        //System.out.println("current max VR number: " + this.maxVRNumber);
        //System.out.println("current code block's maxlive: " + this.maxLive);
        //System.out.println("current SRToVR: " );
        // for (int value : SRToVR){
            
        //     System.out.print(String.format("%d, ", value));
        //     System.out.println();
        // }

    }
    private void printRenamedIR(boolean printVR, boolean printPR){
        OpRecord curOp = this.IRHead.getNext();
        while (curOp != null){
            Opcode opCode = curOp.getOpCode();
            Integer operand1Register = null;
            Integer operand1Constant = null;
            Integer operand2Register = null;
            Integer operand3Register = null;
            if (curOp.getOperand1() != null) {
                if (printVR) {
                    operand1Register = curOp.getOperand1().getVR();
                } else if (printPR) {
                    operand1Register = curOp.getOperand1().getPR();
                }
                operand1Constant = curOp.getOperand1().getSR();
            }
            if (curOp.getOperand2() != null) {
                if (printVR) {
                    operand2Register = curOp.getOperand2().getVR();
                } else if (printPR) {
                    operand2Register = curOp.getOperand2().getPR();
                }
            }
            if (curOp.getOperand3() != null) {
                if (printVR) {
                    operand3Register = curOp.getOperand3().getVR();
                } else if (printPR) {
                    operand3Register = curOp.getOperand3().getPR();
                }
            }

            switch (curOp.getOpCode()) {
                case load:
                    System.out.println(String.format("%s r%d => r%d", opCode, operand1Register, operand3Register));
                    break;
                case loadI:
                    System.out.println(String.format("%s %d => r%d", opCode, operand1Constant, operand3Register));
                    break;
                case store:
                    System.out.println(String.format("%s r%d => r%d", opCode, operand1Register, operand3Register));
                    break;
                case add, sub, mult, lshift, rshift:
                    System.out.println(String.format("%s r%d, r%d => r%d", opCode, operand1Register, operand2Register, operand3Register));
                    break;
                case output:
                    System.out.println(String.format("%s %d", opCode, operand1Constant));
                    break;
                case nop:
                    System.out.println(String.format("nop"));
                    break;

            }
            curOp = curOp.getNext();
        }
    }
    /**
     * Parse, rename (VR), then run the scheduler and print scheduled output.
     */
    public void parseRenameAndSchedule(){
        parse();
        renameIR();
        Scheduler scheduler = new Scheduler(this.IRHead.getNext());
        scheduler.printSchedule();
    }
    
    public static void main(String[] args) {
        try {
            String currentPath = new java.io.File(".").getCanonicalPath();
            System.out.println("Current dir:" + currentPath);
        } catch (java.io.IOException e) {
            System.err.println("Error getting canonical path: " + e.getMessage());
        }
        Parser parser = new Parser(new File("/storage-home/z/zy53/comp412/lab2/Compiler_Register_Allocator/test_inputs/cc1.i"));
        parser.parseRenameAndPrintILOC(false, true, 5);
        //parser.parseRenameAndPrintILOC(true, false, 10);
        //parser.parseAndPrintIR();
        

    }
}
