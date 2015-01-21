package view;

/**
 * View for playing the game in Local mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class LocalMode{
    
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
