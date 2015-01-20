package view;

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
    
    private String[] getPlayers() {
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
