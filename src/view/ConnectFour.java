package view;

import controller.Server;
import controller.Client;
import controller.LocalGame;

/**
 * Main application for ConnectFour.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ConnectFour {

	/**
	 * Starts a local game. Has to run the LocalGame class.
	 */
	private static void playLocal() {
		Runnable play = new LocalGame();
		play.run();
	}

	/**
	 * Starts a Client to play a multiplayer game.
	 */
	private static void playMulti() {
		Client client = new Client();
		Thread t = new Thread(client);
		t.start();
	}

	/**
	 * Lets the user choose if he / she wants to play a local game or a multiplayer game.
	 */
	private static void playGame() {
		String playmode = StandardInput
						.readChoice(
						"\n> Do you want to play a local or "
						+ "a multiplayer game? (local/multi)? \n",
						"local", "multi");
		if (playmode.equals("local")) {
			playLocal();
		} else {
			playMulti();
		}
	}

	/**
	 * Starts a server.
	 */
	private static void startServer() {
		String[] features = new String[0];
		Thread server = new Server(features);
		server.start();
	}

	/**
	 * Let's the user choose if he / she wants to play or wants to start a server.
	 * 
	 * @param args
	 *            starting arguments for this program. Nothing is done with it.
	 */
	public static void main(String[] args) {
		String start = StandardInput
						.readChoice(
						"\n> Do you want to start a server, or "
						+ "do you want to play? (server/play)? \n",
						"server", "play");
		if (start.equals("server")) {
			startServer();
		} else {
			playGame();
		}
	}

}
