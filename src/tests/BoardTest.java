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
		board.setField(0, 1, Mark.BLU);
		board.setField(0, 2, Mark.RED);
		assertEquals(board.getField(0, 0), Mark.XXX);
		assertEquals(board.getField(0, 1), Mark.BLU);
		assertEquals(board.getField(0, 2), Mark.RED);
	}
	
	@Test
	public void testIsEmptyField1(){
		board.setField(1, Mark.BLU);
		board.setField(2, Mark.RED);
		assertFalse(board.isEmptyField(1));
		assertFalse(board.isEmptyField(2));
		assertTrue(board.isEmptyField(3));
	}
	
	@Test
	public void testIsEmptyField2(){
		
	}
}
