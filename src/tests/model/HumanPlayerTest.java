package tests.model;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import model.*;
import view.StandardInput;

/**
 * Test for a Human Player.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class HumanPlayerTest {
	
	private Board board;
	private HumanPlayer player1;
	
	
	// -- Set up -----------------------------------------------------
	
	@Before
	public void setUp() throws Exception {
		board = new Board();
		player1 = new HumanPlayer("Mark", Mark.RED);
	}
	
	
	// -- Tests ------------------------------------------------------
	
	/*
	 * Steps to get best coverage: 1) fill in a valid move (not column 1,
	 * because it is full!). 2) fill in column 1 (full column) 3) fill in an
	 * invalid colum (like 1234) 4) fill in the move you have inserted in step 1
	 */
	@Test
	public void testDetermineMove() {
		board.setField(1, Mark.RED);
		board.setField(8, Mark.BLU);
		board.setField(15, Mark.RED);
		board.setField(22, Mark.BLU);
		board.setField(29, Mark.RED);
		board.setField(36, Mark.RED);
		int first = StandardInput
						.readInt("\n Type the valid choice you are going to test!");
		int second = player1.determineMove(board);
		assertEquals(first, second);
	}

}
