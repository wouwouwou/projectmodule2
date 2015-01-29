package model;

//TODO DONE

/**
 * Class for a Computer Player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class ComputerPlayer extends Player {

	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant strategy != null;
	/**
	 * The strategy of the Computer Player.
	 */
	private Strategy strategy;

	
	// -- Constructors -----------------------------------------------
	
	/*@ requires mark == Mark.RED || mark == Mark.BLU;
	 	ensures getName() != null && getMark() == mark;
	 */
	/**
	 * Creates a Computer Player with a Naive Strategy.
	 * 
	 * @param mark
	 *            the mark which the player will play with
	 */
	public ComputerPlayer(Mark mark) {
		super("Naive computer -", mark);
		strategy = new NaiveStrategy();
	}

	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns the strategy of this Computer Player.
	 * 
	 * @return strategy of the Computer Player
	 */
	//@ pure
	public Strategy getStrategy() {
		return strategy;
	}
	
	/*@ requires board != null && !board.gameOver() && getMark() != null;
	 	ensures \result == getStrategy().determineMove(board, getMark()) &&
	 	board.isEmptyField(\result) && board.isField(\result);
	 */
	/**
	 * Determines the move the Computer Player has to make. Overrides the method
	 * in the abstract Player class.
	 */
	@Override
	//@ pure
	public int determineMove(Board board) {
		return strategy.determineMove(board, this.getMark());
	}

}
