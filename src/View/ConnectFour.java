package view;

import controller.Server;
import controller.Client;
import controller.LocalGame;

/**
 * Main application for ConnectFour.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 *
 */

public class ConnectFour {
	
	/**
	 * Starts the LocalGame Controller.
	 */
	private static void playLocal() {
		Runnable play = new LocalGame();
		play.run();
	}
	
	private static void playMulti() {
		Thread client = new Client();
		Thread clientview = new ClientView();
		client.start();
		clientview.start();
		try {
			clientview.join();
		} catch (InterruptedException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	/**
	 * Lets the user choose if he / she wants to play a local game
	 * or wants to play in multiplayer mode.
	 */
	private static void playGame() {
		String playmode = StandardInput.readChoice("\n> Do you want to play in local-mode or in multiplayer-mode? (local/multi)? \n", "local", "multi");
		if (playmode.equals("local")) {
			playLocal();
		}
		else {
			playMulti();
		}
	}
	
	/**
	 * Starts a server.
	 */
	//TODO Serverview veranderen. Server moet met een peer gaan werken. Tevens shutdown methode aanmaken.
	private static void startServer() {
		Thread server = new Server();
		Thread serverview = new ServerView();
		server.start();
		serverview.start();
		try {
			serverview.join();
		} catch (InterruptedException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		System.out.println("\nServer disconnected.");
		System.exit(0);
	}
	
	/**
	 * Let's the user choose if he / she wants to play or to start a server.
	 * 
	 * @param args
	 * starting arguments for this program. Nothing is done with it.
	 */
	public static void main(String[] args) {
		String start = StandardInput.readChoice("\n> Do you want to start a server, or do you want to play? (server/play)? \n", "server", "play");
		if (start.equals("server")) {
			startServer();
		}
		else {
			playGame();
		}
	}

}
