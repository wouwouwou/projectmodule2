package tests.view;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import view.ConnectFour;

public class ConnectFourTest {
	
	private String[] args;
	
	@Before
	public void setUp() throws Exception {
		args = new String[0];
	}

	@Test
	public void test() {
		ConnectFour.main(args);
	}

}
