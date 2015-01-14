package Model;

/**
 *  Interface for a Strategy of a Computer Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public interface Strategy {
    
	/**
	 * Gets the name of the Strategy.
	 * @return Strategy name.
	 */
    public String getName();
    
    /**
     * Determines the move for the Computer Player. Needs
     * the board and the mark to determine the move.
     * @param b
     *             the board
     * @param m
     *             the mark
     * @return the field
     */
    public int determineMove(Board b, Mark m);

}
