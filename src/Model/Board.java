package model;

/**
 * Board class for the game Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.2
 */
public class Board {

    // -- Constants --------------------------------------------------

    public static final int HEIGHT = 6;
    public static final int WIDTH = 7;
    private static final String[] NUMBERING = 		{"  0  |  1  |  2  |  3  |  4  |  5  |  6  ",
    	"-----+-----+-----+-----+-----+-----+-----", "  7  |  8  |  9  |  10 |  11 |  12 |  13 ",
    	"-----+-----+-----+-----+-----+-----+-----", "  14 |  15 |  16 |  17 |  18 |  19 |  20 ", 
    	"-----+-----+-----+-----+-----+-----+-----", "  21 |  22 |  23 |  24 |  25 |  26 |  27 ", 
    	"-----+-----+-----+-----+-----+-----+-----", "  28 |  29 |  30 |  31 |  32 |  33 |  34 ", 
    	"-----+-----+-----+-----+-----+-----+-----", "  35 |  36 |  37 |  38 |  39 |  40 |  41 "};
    private static final String LINE = NUMBERING[1];

    // -- Instance variables -----------------------------------------

    /*@
       private invariant fields.length == WIDTH*HEIGHT;
       invariant (\forall int i; 0 <= i & i < WIDTH*HEIGHT;
           getField(i) == Mark.XXX || getField(i) == Mark.RED || getField(i) == Mark.BLU);
     */
    /**
     * The fields of the Board. See NUMBERING for the coding of the fields.
     */
    private Mark[] fields;

    // -- Constructors -----------------------------------------------

    /*@
       ensures (\forall int i; 0 <= i & i < WIDTH * HEIGHT; this.getField(i) == Mark.XXX);
     */
    /**
     * Creates an empty Board.
     */
    public Board() {
    	int i = 0;
    	fields = new Mark[(WIDTH * HEIGHT)];
    	do {
    	    fields[i] = Mark.XXX;
    	    i = i + 1;
    	} while (i < (WIDTH * HEIGHT));
    }

    // -- Queries ----------------------------------------------------

    /*@
       ensures \result != this;
       ensures (\forall int i; 0 <= i & i < WIDTH * HEIGHT; \result.getField(i) == this.getField(i));
     */
    /**
     * Creates a deep copy of this Board.
     * 
     * @return Returns a copy of this Board.
     */
    public Board deepCopy() {
        	Board copy = new Board();
        	int i = 0;
        	while (i < WIDTH * HEIGHT) {
        		copy.setField(i, this.getField(i));
        		i++;
        	}
            return copy;
    }


    /*@
       requires 0 <= row & row < WIDTH;
       requires 0 <= col & col < HEIGHT;
     */
    /**
     * Calculates the index in the linear array of fields from a (row, col) pair.
     * 
     * @param row
     * the row
     *             
     * @param col
     * the column
     *             
     * @return the index belonging to the (row,col)-field
     */
    public int index(int row, int col) {
    	int i = (7*row) + col;
        return i;
    }
    
    /*@
    	requires 0 <= i & i < WIDTH * HEIGHT;
     */
    /**
     * Calculates the row and the col of the field from an index. Returns it in an int[].
     * int[0] should return the col. int[1] should return the row.
     * 
     * @param i
     * the index of the field.
     * 
     * @return the col and the row of the field with index i.
     */
    /* Method isn't used yet. Outcommented for a while.

    public int[] getRowCol(int i) {
    	int col = i%7;
    	int row = (i - col) / 7;
    	int[] res = new int[]{row, col};
    	return res;
    }
    
    */
    
    /*@
       ensures \result == (0 <= i && i < WIDTH * HEIGHT);
     */
    /**
     * Returns true if <code>i</code> is a valid index of a field on this Board.
     * 
     * @param i
     * the index of the field.
     * 
     * @return <code>true</code> if <code>0 <= i < HEIGHT * WIDTH</code>
     */
    /*@pure*/
    public boolean isField(int i) {
    	return (0 <= i && i < WIDTH * HEIGHT);
    }

    /*@
       ensures \result == (0 <= row && row < WIDTH && 0 <= col && col < HEIGHT);
     */
    /**
     * Returns true of the (row,col) pair refers to a valid field on this Board.
     * 
     * @param row
     * the row
     * 
     * @param col
     * the column
     * 
     * @return true if <code>0 <= row < HEIGHT && 0 <= col < WIDTH</code>
     */
    /*@pure*/
    public boolean isField(int row, int col) {
        return (0 <= row && row < HEIGHT && 0 <= col && col < WIDTH);
    }


    /*@
       requires this.isField(i);
       ensures \result == Mark.XXX || \result == Mark.RED || \result == Mark.BLU;
     */
    /**
     * Returns the content of the field <code>i</code>.
     * 
     * @param i
     * the number of the field (see NUMBERING)
     *            
     * @return the mark on the field
     */
    public Mark getField(int i) {
    	return fields[i]; 
    }

    /*@
       requires this.isField(row,col);
       ensures \result == Mark.XXX || \result == Mark.RED || \result == Mark.BLU;
     */
    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * 
     * @param row
     * the row of the field
     *            
     * @param col
     * the column of the field
     *            
     * @return the mark on the field
     */
    public Mark getField(int row, int col) {
    	return fields[index(row, col)];
    }

    /*@
       requires this.isField(i);
       ensures \result == (this.getField(i) == Mark.XXX);
     */
    /**
     * Returns true if the field <code>i</code> is empty.
     * 
     * @param i
     * the index of the field (see NUMBERING)
     *            
     * @return true if the field is empty
     */
    public boolean isEmptyField(int i) {
        return getField(i) == Mark.XXX;
    }

    /*@
	   requires this.isField(i);
	   ensures \result == (this.getField(i) == Mark.XXX);
	 */
	/**
	 * Returns true if the field <code>i</code> is empty.
	 * 
	 * @param i
	 * the index of the field (see NUMBERING)
	 *            
	 * @return true if the field is empty
	 */
	public boolean isEmptyField(int i) {
	    return getField(i) == Mark.XXX;
	}

	/*@
       requires this.isField(row,col);
       ensures \result == (this.getField(row,col) == Mark.XXX);

     */
    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     * 
     * @param row
     * the row of the field
     *            
     * @param col
     * the column of the field
     *            
     * @return true if the field is empty
     */
    /*@pure*/
    public boolean isEmptyField(int row, int col) {
        return getField(row, col) == Mark.XXX;
    }
    
    /*@
    	ensures \result == (0 <= col && col < WIDTH);
    */
    /**
     * Returns true if <code>i</code> is a valid column of this board.
     * 
     * @param col
     * the column
     * 
     * @return <code>true</code> if <code>0 <= i < WIDTH</code>
     */
    /*@pure*/
	public boolean isColumn(int col) {
		return (0 <= col && col < WIDTH);
	}
    
    /*@
    	requires this.isColumn(col);
     */
    /**
     * Returns true if the column contains an empty field.
     * 
     * @param col
     * the column
     *
     * @return true if the column contains an empty field
     */
    public boolean containsEmptyColumn(int col) {
    	int row = 0;
    	while (row < HEIGHT) {
    		if (getField(row, col) == Mark.XXX) {
    			return true;
    		}
    		row++;
    	}
    	return false;
    }
    
    /*@
		requires this.isColumn(col);
     */
    /**
     * When a player makes a move, this method determines the field where the Mark will be placed.
     * 
     * @param col
     * the column
     * 
     * @return lowest field on the board. (highest index, highest row)
     */
    public int determineField(int col) {
    	int row = HEIGHT - 1;
    	while (row >= 0) {
    		if (getField(row, col) == Mark.XXX) {
    			break;
    		}
    		row--;
    	}
    	return index(row, col);
    }
    
    /*@
       ensures \result == (\forall int i; i <= 0 & i < WIDTH * HEIGHT; this.getField(i) != Mark.XXX);
     */
    /**
     * Tests if the whole Board is full.
     * 
     * @return true if all fields are occupied
     */
    /*@pure*/
    public boolean isFull() {
    	int i = 0;
    	while (isField(i)) {
    	    if (getField(i) == Mark.XXX) {
    		return false;
    	    }
    	    i++;
    	}
    	return true;
    }

    /*@
       ensures \result == this.isFull() || this.hasWinner();

     */
    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole Board is full.
     * 
     * @return true if the game is over
     */
    /*@pure*/
    public boolean gameOver() {
    	return (isFull() || hasWinner());
    }

    /**
     * Checks whether there is a row which connects four marks <code>m</code>.
     * 
     * @param m
     * the mark of interest
     *
     * @return true if there is a row which connects four marks <code>m</code>
     */
    public boolean hasRow(Mark m) {
    	int row = 0;
    	while(row < HEIGHT){
    		int col = 0;
    		int counter = 0;
    		while(col < WIDTH){
    			if(getField(row, col) == m){
    				counter++;
    			}
    			if(getField(row, col) != m){
    				counter = 0;
    			}
    			if(counter == 4){
    				return true;
    			}
    			if((WIDTH - col) < (4 - counter)){
    				break;
    			}
    			col++;
    		}
    		row++;
    	}
    	return false;
    }

    /**
     * Checks whether there is a column which connects four marks <code>m</code>.
     * 
     * @param m
     * the mark of interest
     *            
     * @return true if there is a column which connects four marks <code>m</code>
     */
    public boolean hasColumn(Mark m) {
    	int col = 0;
    	while (col < WIDTH) {
    		int row = 0;
    		int counter = 0;
    		while (row < HEIGHT) {
    			if (getField(row, col) == m) {
    				counter++;
    			}
    			if (getField(row, col) != m) {
    				counter = 0;
    			}
    			if (counter == 4) {
    				return true;
    			}
    			if ((HEIGHT - row) < 4 - counter) {
    				break;
    			}
    			row++;
    		}
    		col++;
    	}
    	return false;
    }

    /**
     * Checks whether there is a diagonal which connects four marks <code>m</code>.
     * 
     * @param m
     * the mark of interest
     *            
     * @return true if there is a diagonal which connects four marks <code>m</code>
     */
    public boolean hasDiagonal(Mark m) {
    	int count = 0;
    	for(int i = 0; i < WIDTH * HEIGHT; i++){
    		if(i < 3 * WIDTH){
    			if(i % 7 < 3){
    				if(checkDiagonalLeftRight(m, i)){
    					count++;
    				}
        		}
        		else if(i % 7 == 3){
        			if(checkDiagonalLeftRight(m, i) || checkDiagonalRightLeft(m, i)){
        				count++;
        			}
        		}
        		else{
        			if(checkDiagonalRightLeft(m, i)){
        				count++;
        			}
        		}
    		}
    		
    	}
    	return count > 0;
    }
    
    /**
     * Checks whether the given Diagonal at field[i] from the top left to the
     * bottom right of the Board connects four Marks m.
     * 
     * @param m
     * the mark of interest
     *             
     * @param i
     * the beginning field of the Diagonal
     *             
     * @return true if this diagonal connects four Marks m
     */
    public boolean checkDiagonalLeftRight(Mark m, int i) {
    	return (getField(i) == m && getField(i+8) == m && getField(i+16) == m && getField(i+24) == m);
    }
    
    /**
     * Checks whether the given Diagonal at field[i] from the top right to the
     * bottom left of the Board connects four Marks m.
     * 
     * @param m
     * the mark of interest
     *             
     * @param i
     * the beginning field of the Diagonal
     *             
     * @return true if this diagonal connects four Marks m
     */
    public boolean checkDiagonalRightLeft(Mark m, int i) {
    	return (getField(i) == m && getField(i+6) == m && getField(i+12) == m && getField(i+18) == m);
    }
    
    /*@
       requires m == Mark.RED | m == Mark.BLU;
       ensures \result == this.hasRow(m) ||
                                this.hasColumn(m) |
                                this.hasDiagonal(m);
     */
    /**
     * Checks if the mark <code>m</code> has won. A mark wins if it connects four
     * vertically, horizontally or diagonally
     * 
     * @param m
     * the mark of interest
     *            
     * @return true if the mark has won
     */
    /*@pure*/
    public boolean isWinner(Mark m) {
        return (hasColumn(m) || hasRow(m) || hasDiagonal(m));
    }

    /*@
       ensures \result == isWinner(Mark.RED) | \result == isWinner(Mark.BLU);

     */
    /**
     * Returns true if the game has a winner. This is the case when one of the
     * marks connects four vertically, horizontally or diagonally.
     * 
     * @return true if the Board has a winner.
     */
    /*@pure*/
    public boolean hasWinner() {
        return (isWinner(Mark.RED) || isWinner(Mark.BLU));
    }

    /**
     * Returns a String representation of this Board. In addition to the current
     * situation, the String also shows the numbering of the columns.
     * 
     * @return the game situation as String
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < HEIGHT; i++) {
            String row = "";
            for (int j = 0; j < WIDTH; j++) {
                row = row + " " + getField(i, j).toString() + " ";
                if (j < WIDTH - 1) {
                    row = row + "|";
                }
            }
            s = s + row;
            if (i < HEIGHT - 1) {
                s = s + "\n" + LINE + "\n";
            }
        }
        s = s + "\n" + LINE + "\n" + NUMBERING[0];
        return s;
    }

    // -- Commands ---------------------------------------------------

    /*@
     	ensures (\forall int i; 0 <= i & i < WIDTH * HEIGHT; this.getField(i) == Mark.XXX);
     */
    /**
  	* Empties all fields of this Board (i.e., let them refer to the value
  	* Mark.XXX).
  	*/
    public void reset() {
     	for (int i = 0; i < WIDTH * HEIGHT; i++) {
         	fields[i] = Mark.XXX;
     	}
 	}

    /*@
       requires this.isField(i);
       ensures this.getField(i) == m;
     */
    /**
     * Sets the content of field <code>i</code> to the mark <code>m</code>.
     * 
     * @param i
     * the field number (see NUMBERING)
     *            
     * @param m
     * the mark to be placed
     */
    public void setField(int i, Mark m) {
    	fields[i] = m;
    }

    /*@
       requires this.isField(row,col);
       ensures this.getField(row,col) == m;

     */
    /**
     * Sets the content of the field represented by the (row,col) pair to the
     * mark <code>m</code>.
     * 
     * @param row
     * the field's row
     *            
     * @param col
     * the field's column
     *            
     * @param m
     *the mark to be placed
     */
    public void setField(int row, int col, Mark m) {
    	fields[index(row, col)] = m;
    }

}
