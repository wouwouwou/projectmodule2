package tests;

import static org.junit.Assert.*;
import org.junit.*;
import model.*;

public class BoardTest {
    private Board board;
    
    // Sets the board to an empty board.
	@Before
	public void setUp() throws Exception {
		board = new Board();
	}
	// Tests whether the board is really empty.
	@Test
	public void testInitialState() {
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			assertEquals(board.getField(i), Mark.XXX);
		}
	}
	
	// Tests whether the deepcopy really gives a copy of the board as it is at that time.
	@Test
	public void testDeepcopy(){
		Board board1 = board.deepCopy();
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			assertEquals(board.getField(i), board1.getField(i));
		}
	}
	
	//Tests whether the index gives the right index when the row and column are given.
	@Test
	public void testIndex(){
		int a = 1;
		int b = 1;
		assertEquals(board.index(a,b), 8);
		a = 3;
		b = 3;
		assertEquals(board.index(a,b), 24);
		a = 100;
		b = 100;
		assertEquals(board.index(a,b), 800);
	}
	
	// Tests whether really only the fields that are meant to be checked are selected. 
	@Test
	public void testIsField1(){
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			assertTrue(board.isField(i));
		}
		for(int i = Board.WIDTH * Board.HEIGHT; i < 2 * Board.WIDTH * Board.HEIGHT; i++){
			assertFalse(board.isField(i));
		}
		for(int i = -20; i < 0; i++){
			assertFalse(board.isField(i));
		}
	}
	
	//Tests whether only the columns and rows which are meant to be in the board are allowed.
	@Test
	public void testIsField2(){
		for(int i = 0; i < Board.WIDTH; i++){
			for(int j = 0; j < Board.HEIGHT; j++){
				assertTrue(board.isField(j,i));
			}
			for(int j = Board.HEIGHT; j < 100; j++){
				assertFalse(board.isField(j,i));
			}
			for(int j = -20; j < 0; j++){
				assertFalse(board.isField(j,i));
			}
		}
		for(int i = Board.WIDTH; i < 100; i++){
			for(int j = Board.HEIGHT; j < 100; j++){
				assertFalse(board.isField(j,i));
			}
			for(int j = 0; j < Board.HEIGHT; j++){
				assertFalse(board.isField(j,i));
			}
			for(int j = -20; j < 0; j++){
				assertFalse(board.isField(j,i));
			}
		}
		for(int i = 0; i < Board.HEIGHT; i++){
			for(int j = 0; j < Board.WIDTH; j++){
				assertTrue(board.isField(i,j));
			}
			for(int j = Board.WIDTH; j < 100; j++){
				assertFalse(board.isField(i,j));
			}
			for(int j = -20; j < 0; j++){
				assertFalse(board.isField(j,i));
			}
		}
		for(int i = Board.HEIGHT; i < 100; i++){
			for(int j = Board.WIDTH; j < 100; j++){
				assertFalse(board.isField(i,j));
			}
			for(int j = 0; j < Board.WIDTH; j++){
				assertFalse(board.isField(i,j));
			}
			for(int j = -20; j < 0; j++){
				assertFalse(board.isField(j,i));
			}
		}
	}
	
	// Tests whether the right thing in the right field is given.
	@Test
	public void testGetField1(){
		board.setField(1, Mark.BLU);
		board.setField(2, Mark.RED);
		assertEquals(board.getField(0), Mark.XXX);
		assertEquals(board.getField(1), Mark.BLU);
		assertEquals(board.getField(2), Mark.RED);
		
	}
	
	// Tests whether the right thing in the right field is given.
	@Test
	public void testGetField2(){
		board.setField(5, 1, Mark.BLU);
		board.setField(5, 2, Mark.RED);
		assertEquals(board.getField(5, 0), Mark.XXX);
		assertEquals(board.getField(5, 1), Mark.BLU);
		assertEquals(board.getField(5, 2), Mark.RED);
	}
	
	// Tests whether the querry gives the right boolean when a field is selected.
	@Test
	public void testIsEmptyField1(){
		board.setField(1, Mark.BLU);
		board.setField(2, Mark.RED);
		assertTrue(board.isEmptyField(0));
		assertFalse(board.isEmptyField(1));
		assertFalse(board.isEmptyField(2));
	}
	
	// Tests whether the querry gives the right boolean when a field is selected.
	@Test
	public void testIsEmptyField2(){
		board.setField(5, 1, Mark.BLU);
		board.setField(5, 2, Mark.RED);
		assertTrue(board.isEmptyField(5, 0));
		assertFalse(board.isEmptyField(5, 1));
		assertFalse(board.isEmptyField(5, 2));
	}
	
	// Tests whether it allows the right colums.
	@Test
	public void testIsColumn(){
		for(int i = 0; i < Board.WIDTH; i++){
			assertTrue(board.isColumn(i));
		}
		for(int i = Board.WIDTH; i < 100; i++){
			assertFalse(board.isColumn(i));
		}
		for(int i = -20; i < 0; i++){
			assertFalse(board.isColumn(i));
		}
	}
	
	// Tests whether a column still has an empty field.
	@Test
	public void testContainsEmptyColumn(){
		board.setField(5, 1, Mark.BLU);
		board.setField(4, 1, Mark.RED);
		board.setField(3, 1, Mark.BLU);
		board.setField(2, 1, Mark.RED);
		board.setField(1, 1, Mark.BLU);
		board.setField(0, 1, Mark.RED);
		board.setField(5, 2, Mark.BLU);
		board.setField(4, 2, Mark.RED);
		board.setField(3, 2, Mark.BLU);
		board.setField(2, 2, Mark.RED);
		board.setField(1, 2, Mark.BLU);
		board.setField(0, 2, Mark.RED);
		assertTrue(board.containsEmptyColumn(0));
		assertFalse(board.containsEmptyColumn(1));
		assertFalse(board.containsEmptyColumn(2));
	}
	
	// Tests whether the right field is selected by the querry.
	@Test
	public void testDetermineField() {
		board.setField(5, 1, Mark.BLU);
		board.setField(5, 2, Mark.BLU);
		board.setField(4, 2, Mark.BLU);
		board.setField(3, 2, Mark.RED);
		board.setField(2, 2, Mark.BLU);
		board.setField(1, 2, Mark.RED);
		assertEquals(board.determineField(0), board.index(5, 0));
		assertEquals(board.determineField(1), board.index(4, 1));
		assertEquals(board.determineField(2), board.index(0, 2));
	}
	
	// Tests whether the querry gives the correct boolean when the board is full and when the board is not full.
	@Test
	public void testIsFull() {
		assertFalse(board.isFull());
		for(int i = 0; i < Board.WIDTH; i++){
			for(int j = 0; j < Board.HEIGHT; j++){
				if(i % 2 == 0){
					if(j % 2 == 0){
						board.setField(j, i, Mark.RED);
					}
					else{
						board.setField(j, i, Mark.BLU);
					}
				}
				else{
					if(j % 2 == 1){
						board.setField(j, i, Mark.BLU);
					}
					else{
						board.setField(j, i, Mark.RED);
					}
				}
			}
		}
		assertTrue(board.isFull());
	}
	
	// Tests whether 
	@Test
	public void testHasRow() {
		assertFalse(board.hasRow(Mark.RED));
		assertFalse(board.hasRow(Mark.BLU));
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 1 || i == 2 || i == 3){
				board.setField(i, Mark.BLU);
			}
			else if(i == 7 || i == 8 || i == 9 || i == 10){
				board.setField(i, Mark.RED);
			}
		}
		assertTrue(board.hasRow(Mark.RED));
		assertTrue(board.hasRow(Mark.BLU));
	}
	
	@Test
	public void testHasColumn() {
		assertFalse(board.hasColumn(Mark.BLU));
		assertFalse(board.hasColumn(Mark.RED));
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 7 || i == 14 || i == 21){
				board.setField(i, Mark.BLU);
			}
			else if(i == 1 || i == 8 || i == 15 || i == 22){
				board.setField(i, Mark.RED);
			}
		}
		assertTrue(board.hasColumn(Mark.BLU));
		assertTrue(board.hasColumn(Mark.RED));
	}

	@Test
	public void testHasDiagonal() {
		assertFalse(board.hasDiagonal(Mark.BLU));
		assertFalse(board.hasDiagonal(Mark.RED));
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 8 || i == 16 || i == 24){
				board.setField(i, Mark.BLU);
			}
			else if(i == 13 || i == 19 || i == 25 || i == 31){
				board.setField(i, Mark.RED);
			}
		}
		assertTrue(board.hasDiagonal(Mark.RED));
		assertTrue(board.hasDiagonal(Mark.BLU));
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 3 || i == 9 || i == 15 || i == 21){
				board.setField(i, Mark.BLU);
			}
			else if(i == 10 || i == 18 || i == 26 || i == 34){
				board.setField(i, Mark.RED);
			}
		}
		assertTrue(board.hasDiagonal(Mark.BLU));
		assertTrue(board.hasDiagonal(Mark.RED));
	}
	
	@Test
	public void testGameOver() {
		assertFalse(board.gameOver());
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 1 || i == 2 || i ==3){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.gameOver());
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 7 || i == 14 || i == 21){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.gameOver());
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 8 || i == 16 || i == 24){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.gameOver());
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 6 || i == 12 || i == 18 || i == 24){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.gameOver());
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			if(i == 0 || i == 7 || i == 14 || i == 21){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.gameOver());
		for(int i = 0; i < Board.WIDTH; i++){
			for(int j = 0; j < Board.HEIGHT; j++){
				if(i % 2 == 0){
					if(j % 2 == 0){
						board.setField(j, i, Mark.RED);
					}
					else{
						board.setField(j, i, Mark.BLU);
					}
				}
				else{
					if(j % 2 == 1){
						board.setField(j, i, Mark.BLU);
					}
					else{
						board.setField(j, i, Mark.RED);
					}
				}
			}
		}
		assertTrue(board.gameOver());
	}
	
	@Test
	public void testIsWinner() {
		assertFalse(board.isWinner(Mark.BLU));
		assertFalse(board.isWinner(Mark.RED));
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i < 4){
				board.setField(i, Mark.BLU);
			}
			else if(i > 6 && i < 11){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.isWinner(Mark.BLU));
		assertTrue(board.isWinner(Mark.RED));
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i == 0|| i == 7 || i == 14 || i == 21){
				board.setField(i, Mark.BLU);
			}
			else if(i == 1 || i == 8 || i == 15 || i == 22){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.isWinner(Mark.BLU));
		assertTrue(board.isWinner(Mark.RED));
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i == 0|| i == 8 || i == 16 || i == 24){
				board.setField(i, Mark.BLU);
			}
			else if(i == 13 || i == 19 || i == 25 || i == 31){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.isWinner(Mark.BLU));
		assertTrue(board.isWinner(Mark.RED));
	}
	
	// nog 1 branch gemist. Dit is waarschijnlijk de branch die true geeft wanneer ze beide waar zijn maar daar hoeft niet op getest te worden.
	@Test
	public void testHasWinner() {
		assertFalse(board.hasWinner());
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i < 4){
				board.setField(i, Mark.BLU);
			}
			else if(i > 6 && i < 11){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.hasWinner());
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i == 0|| i == 7 || i == 14 || i == 21){
				board.setField(i, Mark.BLU);
			}
			else if(i == 1 || i == 8 || i == 15 || i == 22){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.hasWinner());
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			if(i == 0|| i == 8 || i == 16 || i == 24){
				board.setField(i, Mark.BLU);
			}
			else if(i == 13 || i == 19 || i == 25 || i == 31){
				board.setField(i, Mark.RED);
			}
			else{
				board.setField(i, Mark.XXX);
			}
		}
		assertTrue(board.hasWinner());
	}
	
	@Test
	public void testToString() {
		String method = board.toString();
		String[] numbering = {"  0  |  1  |  2  |  3  |  4  |  5  |  6  ",
		    	"-----+-----+-----+-----+-----+-----+-----"};
		String line = numbering[1];
        String s = "";
        for (int i = 0; i < Board.HEIGHT; i++) {
            String row = "";
            for (int j = 0; j < Board.WIDTH; j++) {
                row = row + " " + board.getField(i, j).toString() + " ";
                if (j < Board.WIDTH - 1) {
                    row = row + "|";
                }
            }
            s = s + row;
            if (i < Board.HEIGHT - 1) {
                s = s + "\n" + line + "\n";
            }
        }
        s = s + "\n" + line + "\n" + numbering[0];
        assertEquals(method, s);
	}
	
	@Test
	public void testReset() {
		board.setField(8, Mark.RED);
		board.setField(5, Mark.RED);
		board.setField(21, Mark.RED);
		board.setField(32, Mark.RED);
		board.setField(23, Mark.RED);
		board.reset();
		for(int i = 0; i < Board.HEIGHT * Board.WIDTH; i++){
			assertEquals(board.getField(i), Mark.XXX);
		}
	}
	
	@Test
	public void testSetField1(){
		board.setField(1, Mark.BLU);
		assertEquals(board.getField(1), Mark.BLU);
	}
	
	@Test
	public void testSetField2() {
		board.setField(1, 2, Mark.BLU);
		assertEquals(board.getField(1, 2), Mark.BLU);
	}
}
