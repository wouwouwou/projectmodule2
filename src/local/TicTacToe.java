package local;

public class TicTacToe {

    public static void main(String[] args) {
	if (args.length == 2) {
	Player p1 = null;
	Player p2 = null;
	if (args[0].equals("-N")) {
	    p1 = new ComputerPlayer(Mark.XX);
	}
	if (args[1].equals("-N")) {
	    p2 = new ComputerPlayer(Mark.OO);
	}
	if (args[0].equals("-S")) {
	    p1 = new ComputerPlayer(Mark.XX, new SmartStrategy());
	}
	if (args[1].equals("-S")) {
	    p2 = new ComputerPlayer(Mark.OO, new SmartStrategy());
	}
	if (p1 == null) {
	    p1 = new HumanPlayer(args[0], Mark.XX);
	}
	if (p2 == null) {
	    p2 = new HumanPlayer(args[1], Mark.OO);
	}
	Game game = new Game(p1, p2);
	game.start();
	}
    }
}
