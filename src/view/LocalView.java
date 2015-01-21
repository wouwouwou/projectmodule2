package view;

import model.Board;

/**
 * View for playing the game in Local mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class LocalView{
	
	/**
     * Prints the game situation.
     */
    public static void showBoard(Board board) {
        System.out.println("\nCurrent game situation: \n\n" + board.toString()
                + "\n");
    }
    
    /**
     * Asks the player two questions. First question is about playing against an ai or against a human.
     * Second question is about the names of the players.
     * 
     * @return String array with the names of two players. String equals "-N" if a player is an AI.
     */
    public static String[] getPlayers() {
    	String[] args = new String[2]; 
    	String human = StandardInput.readChoice("\n> Do you want to play against an AI or against another human player? (ai/human)?", "ai", "human");
    	if (human.equals("human")) {
    		args[0] = StandardInput.getString("\n> Player 1, what is your name?\n");
    		args[1] = StandardInput.getString("\n> Player 2, what is your name?\n");
    	}
    	else {
    		args[0] = StandardInput.getString("\n> What is your name?\n");
    		args[1] = "-N";
    	}
    	return args;
    }
    
}
