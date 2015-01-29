package model;

//TODO DONE

/**
 * Represents a mark in the Connect Four game. There are three possible values:
 * Mark.XXX, Mark.RED and Mark.BLU.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public enum Mark {
	
	/**
	 * Represents an 'Empty' Mark.
	 */
	XXX,
	
	/**
	 * Represents a 'Red' Mark.
	 */
	RED,
	
	/**
	 * Represents a 'Blue' Mark.
	 */
	BLU;

	/*@ ensures this == Mark.RED ==> \result == Mark.BLU;
	 	ensures this == Mark.BLU ==> \result == Mark.RED;
	 	ensures this == Mark.XXX ==> \result ==	Mark.XXX;
	 */
	/**
	 * Returns the other mark. Useful for a better strategy.
	 * 
	 * @return the other mark if this mark is not XXX, else returns XXX
	 */
	public Mark other() {
		if (this == RED) {
			return BLU;
		} else if (this == BLU) {
			return RED;
		} else {
			return XXX;
		}
	}
}
