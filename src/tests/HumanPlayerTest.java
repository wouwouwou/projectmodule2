package tests;

//TODO Check

import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;
import model.*;
import view.StandardInput;

public class HumanPlayerTest {
	private Board board;
	private HumanPlayer player1;

	@Before
	public void setUp() throws Exception {
		board = new Board();
		player1 = new HumanPlayer("Mark", Mark.RED);
	}

	/*
	 * In console, type first a valid move. Then an invalid move, and then the
	 * valid move you have typed before. Test has to be completed by a person.
	 * To test if a field is filled in if the selected column is not full you
	 * have to type a valid column twice. To test if an invalid column gets an
	 * error you will have to first fill in a valid column to be able to
	 * complete the test and then an invalid column. This wil give and error. We
	 * filled a column to make it full. Now you can test what will happen when a
	 * column is full. You have to type the full column twice.
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
