package view;

/**
 * Main application for ConnectFour.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 *
 */

public class ConnectFour {
	
	public static void main(String[] args) {
		String playmode = LocalMode.readChoice("> Do you want to play in local-mode or in multiplayer-mode? (local/multi)?", "local", "multi");
		if (playmode.equals("local")) {
			Thread play = new LocalMode();
			play.start();
			try {
				play.join();
			} catch (InterruptedException e) {
				System.out.println(e.getMessage());
				e.printStackTrace();
			}
		}
	}

}
