package controller;

//TODO Check

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Scanner;

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

	public Peer(ClientHandler clienthandler) {
		handler = clienthandler;
		try {
			in = new BufferedReader(new InputStreamReader(handler.getSocket()
				.getInputStream()));
		} catch (IOException e) {
			System.out.println("Error when constructing a peer. " + e.getMessage());
			e.printStackTrace();
		}
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
	public Peer(Client cli) {
		client = cli;
		try {
			in = new BufferedReader(new InputStreamReader(client.getSocket()
				.getInputStream()));
		} catch (IOException e) {
			System.out.println("Error when constructing a peer. " + e.getMessage());
			e.printStackTrace();
		}
	}

	private void listenClient() {
		boolean doorgaan = true;
		while (doorgaan) {
			String message = null;
			try {
				message = in.readLine();
			} catch (IOException e) {
				client.shutDown();
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
				case "QUIT":
					doorgaan = false;
					break;
				case "ERROR":
					client.printError(message);
					break;
			}
			scan.close();
		}
	}

	private void listenHandler() {
		boolean doorgaan = true;
		while (doorgaan) {
			String message = null;
			try {
				message = in.readLine();
				handler.getServer().getView().printString(message);
			} catch (IOException e) {
				handler.clientShutDown();
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
					doorgaan = false;
					handler.clientShutDown();
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
		try {
			in.close();
		} catch (IOException e) {
			System.out.println("Error when stopping the Peer: " + e.getMessage());
			e.printStackTrace();
		}
	}
}
