package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Scanner;
import view.ServerView;

/**
 * Peer for recieving messages.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class Peer implements Runnable {

	protected BufferedReader in;
	protected ClientHandler handler;
	protected Client client;

	/**
	 * Constructor. Creates a peer object for a ClientHandler.
	 * 
	 * @param handler
	 *            the ClientHandler
	 * 
	 * @param sock
	 *            the socket of the ClientHandler
	 */

	public Peer(ClientHandler clienthandler) throws IOException {
		handler = clienthandler;
		in = new BufferedReader(new InputStreamReader(handler.getSocket()
				.getInputStream()));
	}

	/**
	 * Constructor. Creates a peer object for a Client.
	 * 
	 * @param client
	 *            the Client
	 * 
	 * @param sock
	 *            the socket of the Client
	 */
	public Peer(Client cli) throws IOException {
		client = cli;
		in = new BufferedReader(new InputStreamReader(client.getSocket()
				.getInputStream()));
	}

	private void listenClient() {
		while (true) {
			String message = null;
			try {
				message = in.readLine();
			} catch (IOException e) {
				client.serverShutDown();
			}
			if (message == null) {
				break;
			}
			Scanner scan = new Scanner(message);
			String command = scan.next();
			switch (command) {
				case "LOBBY":
					client.setLobby(message);
					break;
				case "INVITE":
					client.acceptInvite(message);
					break;
				case "START":
					client.gameStart(message);
					break;
				case "REQUEST":
					client.sendMove();
					break;
				case "MOVE":
					client.setMove(message);
					break;
				case "END":
					client.gameEnd(message);
					break;
				case "ERROR":
					client.printError(message);
					break;
			}
			scan.close();
		}
	}

	private void listenHandler() {
		while (true) {
			String message = null;
			try {
				message = in.readLine();
				ServerView.printMessage(message);
			} catch (IOException e) {
				handler.shutDown();
			}
			if (message == null) {
				break;
			}
			Scanner scan = new Scanner(message);
			String command = scan.next();
			switch (command) {
				case "CONNECT":
					handler.connectClient(message);
					break;
				case "INVITE":
					handler.sendInviteToOpp(message);
					break;
				case "LOBBY":
					handler.sendLobby();
					break;
				case "ACCEPT":
					handler.setupGame(message);
					break;
				case "MOVE":
					handler.checkMove(message);
					break;
				case "ERROR":
					handler.printError(message);
					break;
				case "QUIT":
					handler.shutDown();
					break;
				default:
					handler.sendError("InvalidCommand", "Your Command is invalid!");
			}
			scan.close();
		}
	}

	public void run() {
		if (client != null) {
			listenClient();
		}
		if (handler != null) {
			listenHandler();
		}
	}
}
