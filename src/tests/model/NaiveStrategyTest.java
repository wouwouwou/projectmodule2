package tests.model;

import static org.junit.Assert.*;
import model.Strategy;
import model.NaiveStrategy;
import model.Board;
import model.Mark;
import org.junit.Before;
import org.junit.Test;

/**
 * Test for a Naive Strategy.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class NaiveStrategyTest {
	
	private Strategy strategy;
	private Board board;
	private Mark red;
	private Mark blue;

	
	// -- Set up -----------------------------------------------------
	
	@Before
	public void setUp() throws Exception {
		strategy = new NaiveStrategy();
		board = new Board();
		red = Mark.RED;
		blue = Mark.BLU;
	}
	
	
	// -- Tests ------------------------------------------------------
	
	/*
	 * Looks 11 times if strategy.determineMove() returns a valid move.
	 * Then fills 2 columns.
	 * Then looks again 11 times if strategy.determineMove returns a valid move.
	 */
	@Test
	public void strategyTest() {
		assertEquals(strategy.getName(), "Naive computer -");
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		board.setField(0, red);
		board.setField(7, red);
		board.setField(14, red);
		board.setField(21, blue);
		board.setField(28, red);
		board.setField(35, red);
		board.setField(1, blue);
		board.setField(8, blue);
		board.setField(15, blue);
		board.setField(22, red);
		board.setField(29, blue);
		board.setField(36, blue);
		assertEquals(strategy.getName(), "Naive computer -");
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, red)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
		assertTrue(board.containsEmptyColumn(strategy.determineMove(board, blue)));
	}

}
