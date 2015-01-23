package model;

import view.StandardInput;
import controller.ClientHandler;

/**
 * Class for a Human Player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ClientPlayer extends Player {
	
	private ClientHandler client;
	
    // -- Constructors -----------------------------------------------

    /*@
       requires name != null;
       requires mark == Mark.RED || mark == Mark.BLU;
       ensures this.getName() == name;
       ensures this.getMark() == mark;
    */
    /**
     * Creates a new Human Player.
     * 
     * @param name
     *             The name of the player
     * 
     * @param mark
     *             The mark of the player
     */
    public ClientPlayer(ClientHandler handler, Mark mark) {
        super(handler.getClientName(), mark);
    }
    
    /**
     * Gets the ClientHandler of this Player.
     * 
     * @return ClientHandler
     */
    public ClientHandler getClientHandler() {
    	return client;
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
    /*@pure*/
    public int determineMove(Board board) {
        String prompt = "> " + getName() + " (" + getMark().toString() + ")"
                + ", what is your choice? ";
        int choice = StandardInput.readInt(prompt);
        boolean valid = board.isColumn(choice) && board.containsEmptyColumn(choice);
        while (!valid) {
            System.out.println("ERROR: field " + choice
                    + " is no valid choice.");
            choice = StandardInput.readInt(prompt);
            valid = board.isColumn(choice) && board.containsEmptyColumn(choice);
        }
        return choice;
    }

}
