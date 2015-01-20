package view;

import controller.Server;

/**
 * Main application for ConnectFour.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 *
 */

public class ConnectFour {
	
	private static void playLocal() {
		Runnable play = new LocalMode();
		play.run();
	}
	
	private static void playMulti() {
		Thread play = new MultiMode();
		play.start();
		try {
			play.join();
		} catch (InterruptedException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	private static void playGame() {
		String playmode = StandardInput.readChoice("\n> Do you want to play in local-mode or in multiplayer-mode? (local/multi)? \n", "local", "multi");
		if (playmode.equals("local")) {
			playLocal();
		}
		else {
			playMulti();
		}
	}
	
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
