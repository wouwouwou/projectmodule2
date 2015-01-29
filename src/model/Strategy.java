package model;

/**
 * Interface for a Strategy of a Computer Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public interface Strategy {
	
	
	// -- Queries ----------------------------------------------------
	
	//@ ensures \result != null;
	/**
	 * Gets the name of the Strategy.
	 * 
	 * @return Strategy name.
	 */
	//@ pure
	public String getName();
	
	/*@	requires board != null && !board.isFull();
	 	requires mark == Mark.RED || mark == Mark.BLU;
	 	ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Determines the move for the Computer Player. Needs the board and the mark
	 * to determine the move.
	 * 
	 * @param board
	 *            the board
	 *            
	 * @param mark
	 *            the mark
	 *            
	 * @return the field
	 */
	//@ pure
	public int determineMove(Board board, Mark mark);

}
