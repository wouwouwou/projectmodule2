package view;

import java.util.Scanner;

import controller.LocalGame;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.Mark;
import model.Player;
import model.SmartStrategy;

/**
 * View for playing the game in Local mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class LocalMode extends Thread {
	
	/**
     * Prints a question which can be answered by yes (true) or no (false).
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for yes and no. If the
     * user inputs a different value, the prompt is repeated and the method reads
     * input again.
     * 
     * @param prompt the question to print
     * 
     * @param yes
     * the String corresponding to a yes answer
     *            
     * @param no
     * the String corresponding to a no answer
     *            
     * @return true is the yes answer is typed, false if the no answer is typed
     */
    public static boolean readBoolean(String prompt, String yes, String no) {
        String answer;
        do {
            System.out.print(prompt);
            Scanner in = new Scanner(System.in);
            answer = in.hasNextLine() ? in.nextLine() : null;
        } while (answer == null || (!answer.equals(yes) && !answer.equals(no)));
        return answer.equals(yes);
    }
    
    /**
     * Prints a question which can be answered with two options.
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for the two options. If the
     * user inputs a different value, the prompt is repeated and the method reads
     * input again.
     * 
     * @param prompt 
     * the question to print
     * 
     * @param option1
     * the String corresponding to the first option
     * 
     * @param option2
     * the String corresponding to the second option
     * 
     * @return the option typed.
     */
    public static String readChoice(String prompt, String option1, String option2) {
        String answer;
        do {
            System.out.print(prompt);
            Scanner in = new Scanner(System.in);
            answer = in.hasNextLine() ? in.nextLine() : null;
        } while (answer == null || (!answer.equals(option1) && !answer.equals(option2)));
        return answer;
    }
    
    /**
     * Prints a question which can be answered with a String.
     * After prompting the question on standard out, this method reads a String
     * from standard in and gives it back to the caller.
     * 
     * @param prompt
     * the question to print.
     * 
     * @return the string typed.
     */
    private String getString(String prompt) {
    	String res;
    	do {
			System.out.print(prompt);
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
		} while (res == null);
    	return res;
    }
    
    private String[] getPlayers() {
    	String[] args = new String[2]; 
    	String human = readChoice("> Do you want to play against an AI or against another human player? (ai/human)?", "ai", "human");
    	if (human.equals("human")) {
    		args[0] = getString("> Player 1, what is your name?");
    		args[1] = getString("> Player 2, what is your name?");
    	}
    	else {
    		args[0] = getString("> What is your name?");
    		args[1] = "-N";
    	}
    	return args;
    }

    public void run() {
    	String[] args = getPlayers();
    	if (args.length == 2) {
    		Player p1 = null;
    		Player p2 = null;
    		if (args[0].equals("-N")) {
    			p1 = new ComputerPlayer(Mark.RED);
    		}
    		if (args[1].equals("-N")) {
    			p2 = new ComputerPlayer(Mark.BLU);
    		}
    		
    		/*
			if (args[0].equals("-S")) {
	    		p1 = new ComputerPlayer(Mark.RED, new SmartStrategy());
			}
			if (args[1].equals("-S")) {
	    		p2 = new ComputerPlayer(Mark.BLU, new SmartStrategy());
			}
    		*/
    		
    		if (p1 == null) {
    			p1 = new HumanPlayer(args[0], Mark.RED);
    		}
    		if (p2 == null) {
    			p2 = new HumanPlayer(args[1], Mark.BLU);
    		}
    		LocalGame game = new LocalGame(p1, p2);
    		game.start();
    		try {
    			game.join();
    		} catch (InterruptedException e) {
    			System.out.println(e.getMessage());
    			e.printStackTrace();
    		}
    	}
    }
}
