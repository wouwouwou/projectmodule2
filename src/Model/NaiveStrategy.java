package model;

import java.util.Set;
import java.util.HashSet;

/**
 *  Class for a Naive Strategy of a Computer Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class NaiveStrategy implements Strategy {
	
	/**
	 * The name of the Strategy.
	 */
    private String name = "Naive computer -";
    
    /**
     * Returns the name of the Strategy.
     */
    @Override
    public String getName() {
	return this.name;
    }
    
    /**
     * Determines and returns the move for the Computer Player.
     */
    @Override
    public int determineMove(Board b, Mark m) {
	Set<Integer> emptyColumns = new HashSet<Integer>();
	int i = 0;
	while (b.isColumn(i)) {
	    if (b.containsEmptyColumn(i)) {
		emptyColumns.add(i);
	    }
	    i = i + 1;
	}
	int index = (int)Math.round((emptyColumns.size() - 1) * Math.random());
	Integer[] array = emptyColumns.toArray(new Integer[emptyColumns.size()]);
	return array[index];
    }

}
