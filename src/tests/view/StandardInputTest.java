package tests.view;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import view.StandardInput;

public class StandardInputTest {

	/*
	 * Tests the method readBoolean. You are asked to answer with y or n. If you don't type one of these two the question will be asked again.
	 * If answered correctly your answer will be printed.
	 */
	@Test
	public void readBooleanTest() {
		boolean trueorfalse = StandardInput.readBoolean("Beantwoord dit met y of n alsjeblieft. (y/n)", "y", "n");
		System.out.println(trueorfalse);
	}
	
	/*
	 * Tests the method readChoice. You are asked to answer with Charmander or Squirtle. If you don't type one of these two the question will be asked again.
	 * If answered correctly your answer will be printed.
	 */
	@Test
	public void readChoiceTest() {
		String Pokémon = StandardInput.readChoice("Welke Pokémon wil je: Charmander of Squirtle", "Charmander", "Squirtle");
		System.out.println(Pokémon);
	}
	
	/*
	 * Tests the method readInt. You are asked to answer with an integer. If you answer with something else than an integer the question will e asked again.
	 * The integer you answered will be printed if an integer was your answer.
	 */
	@Test
	public void readIntTest() {
		int getal = StandardInput.readInt("Geef een getal!");
		System.out.println(getal);
	}
	
	/*
	 * Tests the method getString. Prints what you said when anything was typed as an answer. 
	 * The question will be asked again when nothing has been answered.
	 */
	@Test
	public void getStringTest() {
		String praat = StandardInput.getString("Zeg maar iets.");
		System.out.println(praat);
	}

}
