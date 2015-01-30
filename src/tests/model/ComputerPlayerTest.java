package tests.model;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import model.*;

/**
 * Test for a Computer Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class ComputerPlayerTest {
	
	private Board board;
	private ComputerPlayer player1;

	
	// -- Set up -----------------------------------------------------
	
	@Before
	public void setUp() throws Exception {
		board = new Board();
		player1 = new ComputerPlayer(Mark.RED);
	}
	
	
	// -- Tests ------------------------------------------------------
	
	/*
	 * When the coverage of this test is tested, it will show a couple of
	 * branches are missed.These branches are tested in another part of the
	 * test. This test also checks whether the computer doesn't try to fill in a
	 * full column and fills in another column instead.
	 */
	@Test
	public void computerPlayerTest() {
		int count = 0;
		for (int i = 0; i < Board.WIDTH * Board.HEIGHT; i++) {
			if (!(board.getField(i) == Mark.XXX)) {
				count++;
			}
		}
		assertTrue(count == 0);
		player1.makeMove(this.board);
		count = 0;
		for (int i = 0; i < Board.WIDTH * Board.HEIGHT; i++) {
			if (!(board.getField(i) == Mark.XXX)) {
				count++;
			}
		}
		assertFalse(count == 0);
		for (int i = 0; i < Board.HEIGHT * Board.WIDTH - 1; i++) {
			if (i % 2 == 0) {
				board.setField(i, Mark.BLU);
			} else {
				board.setField(i, Mark.BLU);
			}
		}
		player1.makeMove(this.board);
		assertTrue(board.isFull());
		Strategy strat = player1.getStrategy();
		assertNotNull(strat);
		assertEquals(player1.getMark(), Mark.RED);
		assertEquals(player1.getName(), "Naive computer -");
	}

}
