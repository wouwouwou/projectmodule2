package Model;

/**
 * Board class for the game Connect Four.
 * 
 * @author Jan-Jaap van Raffe & Wouter Bos
 * @version 1.0
 */
public class Board {

    // -- Constants --------------------------------------------------

    public static final int HEIGHT = 6;
    public static final int WIDTH = 7;
    private static final String[] NUMBERING = {" 00 | 01 | 02 | 03 | 04 | 05 | 06 ",
    	"----+----+----+----+----+----+----", " 07 | 08 | 09 | 10 | 11 | 12 | 13 ",
    	"----+----+----+----+----+----+----", " 14 | 15 | 16 | 17 | 18 | 19 | 20 ", 
    	"----+----+----+----+----+----+----", " 21 | 22 | 23 | 24 | 25 | 26 | 27 ", 
    	"----+----+----+----+----+----+----", " 28 | 29 | 30 | 31 | 32 | 33 | 34 ", 
    	"----+----+----+----+----+----+----", " 35 | 36 | 37 | 38 | 39 | 40 | 41 ", };
    private static final String LINE = NUMBERING[1];
    private static final String DELIM = "     ";

    // -- Instance variables -----------------------------------------

    /*@
       private invariant fields.length == DIM*DIM;
       invariant (\forall int i; 0 <= i & i < DIM*DIM;
           getField(i) == Mark.EMPTY || getField(i) == Mark.XX || getField(i) == Mark.OO);
     */
    /**
     * The fields of the Board. See NUMBERING for the coding of the fields.
     */
    private Mark[] fields;

    // -- Constructors -----------------------------------------------

    /*@
       ensures (\forall int i; 0 <= i & i < DIM * DIM; this.getField(i) == Mark.EMPTY);
     */
    /**
     * Creates an empty Board.
     */
    public Board() {
    	
    }

    // -- Queries ----------------------------------------------------

    /*@
       ensures \result != this;
       ensures (\forall int i; 0 <= i & i < DIM * DIM; \result.getField(i) == this.getField(i));
     */
    /**
     * Creates a deep copy of this Board.
     */
    public Board deepCopy() {
    	return null;
    }


    /*@
       requires 0 <= row & row < DIM;
       requires 0 <= col & col < DIM;
     */
    /**
     * Calculates the index in the linear array of fields from a (row, col) pair.
     * @return the index belonging to the (row,col)-field
     */
    public int index(int row, int col) {
        return 0;
    }


    /*@
       ensures \result == (0 <= ix && ix < DIM * DIM);
     */
    /**
     * Returns true if <code>i</code> is a valid index of a field on the student.
     * @return <code>true</code> if <code>0 <= ix < HEIGHT * WIDTH</code>
     */
    /*@pure*/
    public boolean isField(int i) {
	return false;
    }

    /*@
       ensures \result == (0 <= row && row < DIM && 0 <= col && col < DIM);
     */
    /**
     * Returns true of the (row,col) pair refers to a valid field on the student.
     * 
     * @return true if <code>0 <= row < HEIGHT && 0 <= col < WIDTH</code>
     */
    /*@pure*/
    public boolean isField(int row, int col) {
        return false;
    }


    /*@
       requires this.isField(i);
       ensures \result == Mark.EMPTY || \result == Mark.XX || \result == Mark.OO;
     */
    /**
     * Returns the content of the field <code>i</code>.
     * 
     * @param i
     *            the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    public Mark getField(int i) {
	    return null; 
    }

    /*@
       requires this.isField(row,col);
       ensures \result == Mark.EMPTY || \result == Mark.XX || \result == Mark.OO;
     */
    /**
     * Returns the content of the field referred to by the (row,col) pair.
     * 
     * @param row
     *            the row of the field
     * @param col
     *            the column of the field
     * @return the mark on the field
     */
    public Mark getField(int row, int col) {
        return null;
    }

    /*@
       requires this.isField(i);
       ensures \result == (this.getField(i) == Mark.EMPTY);
     */
    /**
     * Returns true if the field <code>i</code> is empty.
     * 
     * @param i
     *            the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    public boolean isEmptyField(int i) {
        return false;
    }

    /*@
       requires this.isField(row,col);
       ensures \result == (this.getField(row,col) == Mark.EMPTY);

     */
    /**
     * Returns true if the field referred to by the (row,col) pair it empty.
     * 
     * @param row
     *            the row of the field
     * @param col
     *            the column of the field
     * @return true if the field is empty
     */
    /*@pure*/
    public boolean isEmptyField(int row, int col) {
        return false;
    }

    /*@
       ensures \result == (\forall int i; i <= 0 & i < DIM * DIM; this.getField(i) != Mark.EMPTY);
     */
    /**
     * Tests if the whole Board is full.
     * 
     * @return true if all fields are occupied
     */
    /*@pure*/
    public boolean isFull() {
    	return false;
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
        return false;
    }

    /**
     * Checks whether there is a row which connects four marks <code>m</code>.
     * 
     * @param m
     *            the mark of interest
     * @return true if there is a row which connects four marks <code>m</code>
     */
    public boolean hasRow(Mark m) {
    	return false;
    }

    /**
     * Checks whether there is a column which connects four marks <code>m</code>.
     * 
     * @param m
     *            the mark of interest
     * @return true if there is a column which connects four marks <code>m</code>
     */
    public boolean hasColumn(Mark m) {
    	return false;
    }

    /**
     * Checks whether there is a diagonal which connects four marks <code>m</code>.
     * 
     * @param m
     *            the mark of interest
     * @return true if there is a diagonal which connects four marks <code>m</code>
     */
    public boolean hasDiagonal(Mark m) {
    	return false;
    }

    /*@
       requires m == Mark.XX | m == Mark.OO;
       ensures \result == this.hasRow(m) ||
                                this.hasColumn(m) |
                                this.hasDiagonal(m);
     */
    /**
     * Checks if the mark <code>m</code> has won. A mark wins if it connects four
     * vertically, horizontally or diagonally
     * 
     * @param m
     *            the mark of interest
     * @return true if the mark has won
     */
    /*@pure*/
    public boolean isWinner(Mark m) {
        return false;
    }

    /*@
       ensures \result == isWinner(Mark.XX) | \result == isWinner(Mark.OO);

     */
    /**
     * Returns true if the game has a winner. This is the case when one of the
     * marks connects four vertically, horizontally or diagonally.
     * 
     * @return true if the Board has a winner.
     */
    /*@pure*/
    public boolean hasWinner() {
        return false;
    }

    /**
     * Returns a String representation of this student. In addition to the current
     * situation, the String also shows the numbering of the columns.
     * 
     * @return the game situation as String
     */
    public String toString() {
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                row = row + " " + getField(i, j).toString() + " ";
                if (j < DIM - 1) {
                    row = row + "|";
                }
            }
            s = s + row + DELIM + NUMBERING[i * 2];
            if (i < DIM - 1) {
                s = s + "\n" + LINE + DELIM + NUMBERING[i * 2 + 1] + "\n";
            }
        }
        return s;
    }

    // -- Commands ---------------------------------------------------

    /*@
       ensures (\forall int i; 0 <= i & i < DIM * DIM; this.getField(i) == Mark.EMPTY);
     */
    /**
     * Empties all fields of this Board (i.e., let them refer to the value
     * Mark.XXX).
     */
    public void reset() {
        
    }

    /*@
       requires this.isField(i);
       ensures this.getField(i) == m;
     */
    /**
     * Sets the content of field <code>i</code> to the mark <code>m</code>.
     * 
     * @param i
     *            the field number (see NUMBERING)
     * @param m
     *            the mark to be placed
     */
    public void setField(int i, Mark m) {
    	
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
     *            the field's row
     * @param col
     *            the field's column
     * @param m
     *            the mark to be placed
     */
    public void setField(int row, int col, Mark m) {
    	
    }

}
