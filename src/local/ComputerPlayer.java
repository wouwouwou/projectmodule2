package local;

import local.Board;

public class ComputerPlayer extends Player {
    
    private Strategy strategy;
    
    ComputerPlayer(Mark mark){
	super("Naive computer -", mark);
	strategy = new NaiveStrategy();
    }
    
    ComputerPlayer(Mark mark, Strategy strategy) {
	super(strategy.getName(), mark);
	this.strategy = strategy;
    }
    
    @Override
    public int determineMove(Board board) {
	return strategy.determineMove(board, this.getMark());
    }
    
}
