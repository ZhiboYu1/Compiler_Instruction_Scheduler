import java.io.File;

public class Main {
    public static void main(String[] args) {

        for (int i = 0; i < args.length; i++){
            //System.out.println(String.format("args[%d]: %s", i, args[i]));
        }

        if (args.length == 1){ //either only have -h flag or only have file path
            if (args[0].equals("-h")){
                printCommandDescription();
            } else {
                // Default: run scheduler and print scheduled output
                scanParseFile(args[0], false, false, false, false, -1, true);
            }
        } else if (args.length == 2){
            try {
                int k = Integer.parseInt(args[0]);
                String filePath = args[1];
                scanParseFile(filePath, false, false, false, true, k, false);
            } catch (NumberFormatException e) {
                String flag = args[0];
                String filePath = args[1];
                if (flag.equals("-s")){
                    scanParseFile(filePath, true, false, false, false, -1, false);
                } else if (flag.equals("-p")){
                    scanParseFile(filePath, false, false, false, false, -1, false);//doesn't print IR
                } else if (flag.equals("-r")){
                    scanParseFile(filePath, false, true, false, false, -1, false);
                } else if (flag.equals("-x")){
                    scanParseFile(filePath, false, false, true, false, -1, false);
                } else if (flag.equals("-S")){
                    // schedule using renamed VRs
                    scanParseFile(filePath, false, false, false, false, -1, true);
                } 
            }
            
            
            // else if (flag.equals("-x")){
            //     scanParseFile(filePath, false, true);
            // }
        } else {
            System.err.println("Please input one command line flag for each operation.");
            printCommandDescription();
        }

    }
    /**
     * helper function to parse the file (and print IR) or scan only 
     * @param filePath
     * @param onlyScan
     * @param printIR
     * @param printVR boolean value representing whether we want to print ILOC block with VR values (after renaming and register allocation)
     * @param printPR boolean value representing whether we want to print ILOC block with PR values (after renaming and register allocation)
     * @param k
     */
    private static void scanParseFile(String filePath, boolean onlyScan, boolean printIR, boolean printVR, boolean printPR, int k, boolean schedule){
        File toBeParsedFile = new File(filePath);
        if (toBeParsedFile.exists()){
            if (!onlyScan){
                Parser parser = new Parser(toBeParsedFile);
                if (printIR){
                    parser.parseAndPrintIR();
                } else if (printVR || printPR){
                    //TODO: including k as a parameter might not be a good design
                    parser.parseRenameAndPrintILOC(printVR, printPR, k);
                } else if (schedule) {
                    parser.parseRenameAndSchedule();
                } else {
                    parser.parseAndPrintIR();
                }
            } else {
                Scanner scanner = new Scanner(toBeParsedFile);
                scanner.scanEntireFile();
            }
            
        } else {
            System.err.println("ERROR: File does not exist!");
            printCommandDescription();
        }
    }
    private static void scanParseRenameFile(){

    }
    private static void printCommandDescription(){
        
        System.out.println("  -h \t\t Display this help message.");
        System.out.println("  -s <filename>\t Read the specified file, scan it, and print a list of tokens.");
        System.out.println("  -p <filename>\t Read the specified file, scan it, parse it, and report success or failure.");
        System.out.println("  -r <filename>\t Read the specified file, scan it, parse it, and print the intermediate representation.");
        System.out.println("  -x <filename>\t scans and parse the input block. It should then perform renaming the code in the input block and print the results to the standard output stream.");
        System.out.println("  <int k> <filename>\t  scans and parse the input block. It should then perform renaming, then allocating with the inputted integer representing the number of reserved registers. It then prints the results of the register allocation to the standard output stream.");
        System.out.println("  <name> schedule <name> will be used to invoke schedule on the input block contained in <name> (schedule is the name of the executable). <name> specifics the name of the input file. <name> is a valid Linux pathname relative to the current working directory. shcedule will produce, as output, an ILOC program that is equivalent to the input program, albeit reordered to improve its execution time on the Lab3 ILOC Simulator. The output code must use the square bracket notation [op1;op2] to designate operations that should issue in the same cycle. schedule is not required to process command-line arguments that appear after <file name>.");
        // System.out.println(
        //         "Supported command flags:\n" +
        //         "412alloc –h produce a list of valid command-line arguments that " +
        //             "includes a description of all command-line arguments.\n" +

        //         "412alloc -s <name>: When the -s flag is present, 412fe reads the file specified by <name>" +
        //             "and print, to the standard output stream, a list of the tokens that the scanner found." +
        //             "For each token, it prints the line number, the token’s type (or syntactic category), and its" +
        //             "spelling (or lexeme).\n" +

        //         "412alloc -p <name> When the -p flag is present, 412fe should read the file specified by " +
        //             "<name>, scan it and parse it, build the intermediate representation, and report either success or" +
        //             "report all the errors that it finds in the input file. If the parse succeeds, the front end must" +
        //             "report “Parse succeeded. Processed k operations.”, where k is the number of operations the" +
        //             "front end handled, printed without commas. If it finds errors, it must print “Parse found errors.”" +

        //         "412alloc -r <name> When the -r flag is present, 412fe should read the file specified by <name>," +
        //             "scan it, parse it, build the intermediate representation, and print out the information in the" +
        //             "intermediate representation (in an appropriately human readable format).\n" +

        //         "412alloc -x <name> ith this flag, 412alloc should scan and parse the input block. It\n" + 
        //             "should then perform renaming on the code in the input block and print the results to\n" + 
        //             "the standard output stream (stdout).\n" +

        //         "412alloc k <name> In this format, k is the number of registers available to the allocator \n" +
        //             "(3 ≤ k ≤ 64) and <name> is a Linux pathname to the file containing the input block.\n" +
        //             "The pathname can be either a relative pathname or an absolute pathname."
        // );
    }
}