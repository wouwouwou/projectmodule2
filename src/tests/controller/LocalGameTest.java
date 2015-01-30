package tests.controller;

import static org.junit.Assert.*;
import controller.LocalGame;
import org.junit.Before;
import org.junit.Test;

/**
 * Test for a Local Game.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version 1.0
 */
public class LocalGameTest {
	
	private LocalGame game;
	
	// -- Set up -----------------------------------------------------
	
	@Before
	public void setUp() throws Exception {
		game = new LocalGame();
	}
	
	
	// -- Tests ------------------------------------------------------
	
	@Test
	public void test() {
		game.run();
	}

}
