package model;

import view.StandardInput;

/**
 * Class for a Human Player in Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class HumanPlayer extends Player {

	// -- Constructors -----------------------------------------------

	/*@ requires name != null && (mark == Mark.RED || mark == Mark.BLU);
	  	ensures getName() == name; ensures getMark() == mark;
	 */
	/**
	 * Creates a new Human Player.
	 * 
	 * @param name
	 *            The name of the player
	 * 
	 * @param mark
	 *            The mark of the player
	 */
	public HumanPlayer(String name, Mark mark) {
		super(name, mark);
	}

	// -- Commands ---------------------------------------------------

	/*@ requires board != null && !board.gameOver() && getMark() != null;
	 	ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the standard input/output.
	 * 
	 * @param board
	 *            the game board
	 *            
	 * @return the player's chosen field
	 */
	public int determineMove(Board board) {
		String prompt = "> " + getName() + " (" + getMark().toString() + ")"
						+ ", what is your choice? ";
		int choice = StandardInput.readInt(prompt);
		boolean valid = board.isColumn(choice)
						&& board.containsEmptyColumn(choice);
		while (!valid) {
			System.out.println("ERROR: field " + choice
							+ " is no valid choice.");
			choice = StandardInput.readInt(prompt);
			valid = board.isColumn(choice) && board.containsEmptyColumn(choice);
		}
		return choice;
	}

}
