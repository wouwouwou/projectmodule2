package model;

import java.util.Set;
import java.util.HashSet;

/**
 * Class for a Naive Strategy of a Computer Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class NaiveStrategy implements Strategy {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant name != null;
	/**
	 * The name of the Strategy.
	 */
	private String name = "Naive computer -";
	
	
	// -- Queries ----------------------------------------------------
	
	//@ ensures \result != null;
	/**
	 * Returns the name of the Strategy.
	 */
	@Override
	//@ pure
	public String getName() {
		return name;
	}
	
	/*@	requires board != null && !board.isFull();
 		requires mark == Mark.RED || mark == Mark.BLU;
 		ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Determines and returns the move for the Computer Player.
	 */
	@Override
	//@ pure
	public int determineMove(Board board, Mark mark) {
		Set<Integer> emptyColumns = new HashSet<Integer>();
		int i = 0;
		while (board.isColumn(i)) {
			if (board.containsEmptyColumn(i)) {
				emptyColumns.add(i);
			}
			i = i + 1;
		}
		int index = (int) Math.round((emptyColumns.size() - 1) * Math.random());
		Integer[] array = emptyColumns
				.toArray(new Integer[emptyColumns.size()]);
		return array[index];
	}

}
