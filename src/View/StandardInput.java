package view;

import java.util.Scanner;

import controller.LocalClient;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.Mark;
import model.Player;
import model.SmartStrategy;

public class StandardInput {
	
	/**
     * Prints a question which can be answered by yes (true) or no (false).
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for yes and no. If the
     * user inputs a different value, the prompt is repeated and the method reads
     * input again.
     * 
     * @parom prompt the question to print
     * @param yes
     *            the String corresponding to a yes answer
     * @param no
     *            the String corresponding to a no answer
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

    public static void main(String[] args) {
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
    		LocalClient game = new LocalClient(p1, p2);
    		game.start();
    	}
    }
}
