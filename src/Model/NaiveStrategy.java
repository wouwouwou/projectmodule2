package Model;

import java.util.*;

/**
 *  Class for a Naive Strategy of a Computer Player.
 * 
 * @author Jan-Jaap van Raffe & Wouter Bos
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
	Set<Integer> emptyFields = new HashSet<Integer>();
	int i = 0;
	while (b.isField(i)) {
	    if (b.isEmptyField(i)) {
		emptyFields.add(i);
	    }
	    i = i + 1;
	}
	int index = (int)Math.round((emptyFields.size() - 1) * Math.random());
	Integer[] array = emptyFields.toArray(new Integer[emptyFields.size()]);
	return array[index];
    }

}
