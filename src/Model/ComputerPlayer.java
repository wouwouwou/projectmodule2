package Model;

/**
 *  Class for a Computer Player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class ComputerPlayer extends Player {
	
	// -- Instance variables -----------------------------------------
    
	/**
	 * The strategy of the Computer Player. 
	 */
    private Strategy strategy;
    
    // -- Constructors -----------------------------------------------
    
    /**
     * Creates a Computer Player with a Naive Strategy.
     * 
     * @param mark
     * the mark which the player will play with
     */
    public ComputerPlayer(Mark mark){
    	super("Naive computer -", mark);
    	strategy = new NaiveStrategy();
    }
    
    
    /* Temporarily commented out because of minimal requirements!

    ComputerPlayer(Mark mark, Strategy strategy) {
	super(strategy.getName(), mark);
	this.strategy = strategy;
    }
    
    */
    
    /**
     * Determines the move the Computer Player has to make.
     * Overrides the method in the abstract Player class.
     */
    @Override
    public int determineMove(Board board) {
	return strategy.determineMove(board, this.getMark());
    }
    
}
