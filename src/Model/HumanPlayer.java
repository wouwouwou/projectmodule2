package Model;

import java.util.Scanner;

/**
 * Class for a Human Player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe & Wouter Bos
 * @version v1.0
 */
public class HumanPlayer extends Player {

    // -- Constructors -----------------------------------------------

    /*@
       requires name != null;
       requires mark == Mark.RED || mark == Mark.BLU;
       ensures this.getName() == name;
       ensures this.getMark() == mark;
    */
    /**
     * Creates a new Human Player.
     */
    public HumanPlayer(String name, Mark mark) {
        super(name, mark);
    }

    // -- Commands ---------------------------------------------------

    /*@
       requires board != null;
       ensures board.isField(\result) && board.isEmptyField(\result);
     */
    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output.
     * 
     * @param board
     *            the game board
     * @return the player's chosen field
     */
    public int determineMove(Board board) {
        String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                + ", what is your choice? ";
        int choice = readInt(prompt);
        boolean valid = board.isField(choice) && board.isEmptyField(choice);
        while (!valid) {
            System.out.println("ERROR: field " + choice
                    + " is no valid choice.");
            choice = readInt(prompt);
            valid = board.isField(choice) && board.isEmptyField(choice);
        }
        return choice;
    }

    /**
     * Writes a prompt to standard out and tries to read an int value from
     * standard in. This is repeated until an int value is entered.
     * 
     * @param prompt
     *            the question to prompt the user
     * @return the first int value which is entered by the user
     */
    private int readInt(String prompt) {
        int value = 0;
        boolean intRead = false;
        do {
            System.out.print(prompt);
            Scanner in = new Scanner(System.in);
            String line = in.nextLine();
            Scanner scannerLine = new Scanner(line);
            if (scannerLine.hasNextInt()) {
                intRead = true;
                value = scannerLine.nextInt();
                in.close();
                scannerLine.close();
            }
        } while (!intRead);

        return value;
    }

}