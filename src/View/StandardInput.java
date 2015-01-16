package View;

import Controller.LocalClient;
import Model.ComputerPlayer;
import Model.HumanPlayer;
import Model.Mark;
import Model.Player;
import Model.SmartStrategy;

public class StandardInput {

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
