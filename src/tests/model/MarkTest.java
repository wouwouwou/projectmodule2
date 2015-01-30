package tests.model;

import static org.junit.Assert.*;
import model.Mark;

import org.junit.Before;
import org.junit.Test;

/**
 * Test for a Mark.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class MarkTest {
	
	private Mark empty;
	private Mark red;
	private Mark blue;
	
	
	// -- Set up ----------------------------------------------------
	
	@Before
	public void setUp() throws Exception {
		empty = Mark.XXX;
		red = Mark.RED;
		blue = Mark.BLU;
	}
	
	
	// -- Tests ------------------------------------------------------
	
	@Test
	public void testOther() {
		assertEquals(red.other(), blue);
		assertEquals(blue.other(), red);
		assertEquals(empty.other(), empty);
	}

}
