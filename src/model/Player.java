package model;

/**
 * Abstract class for a player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public abstract class Player {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant name != null;
	/**
	 * The name of the player.
	 */
	private String name;
	
	//@ private invariant name != null;
	/**
	 * The mark of the player.
	 */
	private Mark mark;
	
	
	// -- Constructors -----------------------------------------------

	/*@ requires theName != null && (theMark == Mark.RED || theMark == Mark.BLU);
	 	ensures getName() == theName && getMark() == theMark;
	 */
	/**
	 * Creates a new Player object.
	 * 
	 * @param theName
	 *            the name of the player.
	 * 
	 * @param theMark
	 *            the mark of the player.
	 */
	public Player(String theName, Mark theMark) {
		name = theName;
		mark = theMark;
	}
	
	
	// -- Queries ----------------------------------------------------
	
	//@ ensures \result != null;
	/**
	 * Returns the name of the player.
	 * 
	 * @return Player name
	 */
	//@ pure
	public String getName() {
		return name;
	}
	
	//@ ensures \result == Mark.RED || \result == Mark.BLU;
	/**
	 * Returns the mark of the player.
	 * 
	 * @return Player mark
	 */
	//@ pure
	public Mark getMark() {
		return mark;
	}

	/*@ requires board != null & !board.isFull();
	 	ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Determines the field for the next move.
	 * 
	 * @param board
	 *            the current game board
	 * @return the player's choice
	 */
	//@ pure
	public abstract int determineMove(Board board);
	
	
	// -- Commands ---------------------------------------------------

	//@ requires board != null && !board.isFull();
	/**
	 * Makes a move on the board. <br>
	 * 
	 * @param board
	 *            the current board
	 */
	public void makeMove(Board board) {
		int choice = determineMove(board);
		int i = board.determineField(choice);
		board.setField(i, getMark());
	}
}
