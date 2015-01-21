package tests;

import static org.junit.Assert.*;

import org.junit.*;
import model.Mark;
import model.*;
;
public class BoardTest {
    private Board board;
    
	@Before
	public void setUp() throws Exception {
		board = new Board();
	}

	@Test
	public void testInitialState() {
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			assertEquals(board.getField(i), Mark.XXX);
		}
	}
	
	@Test
	public void testDeepcopy(){
		Board board1 = board.deepCopy();
		for(int i = 0; i < Board.WIDTH * Board.HEIGHT; i++){
			assertEquals(board.getField(i), board1.getField(i));
		}
	}
	
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
	
	//Mist nog 1 branch
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
	
	@Test
	public void testGetField1(){
		board.setField(1, Mark.BLU);
		board.setField(2, Mark.RED);
		assertEquals(board.getField(0), Mark.XXX);
		assertEquals(board.getField(1), Mark.BLU);
		assertEquals(board.getField(2), Mark.RED);
		
	}
	
	@Test
	public void testGetField2(){
		board.setField(5, 1, Mark.BLU);
		board.setField(5, 2, Mark.RED);
		assertEquals(board.getField(5, 0), Mark.XXX);
		assertEquals(board.getField(5, 1), Mark.BLU);
		assertEquals(board.getField(5, 2), Mark.RED);
	}
	
	@Test
	public void testIsEmptyField1(){
		board.setField(1, Mark.BLU);
		board.setField(2, Mark.RED);
		assertTrue(board.isEmptyField(0));
		assertFalse(board.isEmptyField(1));
		assertFalse(board.isEmptyField(2));
	}
	
	@Test
	public void testIsEmptyField2(){
		board.setField(5, 1, Mark.BLU);
		board.setField(5, 2, Mark.RED);
		assertTrue(board.isEmptyField(5, 0));
		assertFalse(board.isEmptyField(5, 1));
		assertFalse(board.isEmptyField(5, 2));
	}
	
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
	
	//1 branch missed.
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
	
	//nog 1 branch gemist.
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
	
	
}
