package controller;

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
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant in != null;
	/**
	 * The input. Used to receive all messages.
	 */
	private BufferedReader in;
	
	/**
	 * Corresponding handler. Can be null if this peer corresponds with a Client.
	 */
	private ClientHandler handler;
	
	/**
	 * Corresponding client. Can be null if this peer corresponds with a ClientHandler.
	 */
	private Client client;
	
	
	// -- Constructors -----------------------------------------------
	
	//@ ensures getHandler() != null;
	/**
	 * Creates a peer object for a ClientHandler. Gets the input from the
	 * handler's socket.
	 * 
	 * @param clienthandler
	 *            the ClientHandler
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
	
	//@ ensures getClient() != null;
	/**
	 * Creates a peer object for a Client. Gets the input from the client's
	 * socket.
	 * 
	 * @param cli
	 *            the Client
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
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Gets the input.
	 * 
	 * @return input
	 */
	//@ pure
	public BufferedReader getInput() {
		return in;
	}
	
	/**
	 * Gets the corresponding ClientHandler.
	 * 
	 * @return ClientHandler
	 */
	//@ pure
	public ClientHandler getHandler() {
		return handler;
	}
	
	/**
	 * Gets the corresponding Client.
	 *  
	 * @return Client
	 */
	//@ pure
	public Client getClient() {
		return client;
	}
	
	//@ ensures \result.equals("Client") || \result.equals("ClientHandler");
	/**
	 * Gets the type of this Peer as a String.
	 * Client means a peer for a client.
	 * ClientHandler means a peer for a ClientHandler.
	 * 
	 * @return String "Client" || String "ClientHandler"
	 */
	//@ pure
	public String getType() {
		boolean cli = false;
		if (getClient() != null) {
			cli = true;
		}
		if (cli) {
			return "Client";
		}
		return "ClientHandler";
	}
	
	// -- Commands ---------------------------------------------------
	
	
	/**
	 * Listens as a client to the input. If a message comes in, looks for the
	 * first word. Calls the method corresponding to the command. More
	 * information is available in the protocol.
	 * 
	 * When the input gives an IOException, shutDown method from the Client will
	 * be called. Also breaks the while loop.
	 */
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
	
	/**
	 * Listens as a handler to the input. If a message comes in, looks for the
	 * first word. Calls the method corresponding to the command. More
	 * information is available in the protocol.
	 * 
	 * When the input gives an IOException, shutDown method from the handler
	 * will be called. Also breaks the while loop.
	 */
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
	
	/**
	 * Runs the peer. If the peer has a client, then listens to the input as a
	 * client. If the peer has a handler, then listens to the input as a
	 * handler. Closes input when done listening.
	 */
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
