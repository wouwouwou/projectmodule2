package controller;

import java.net.Socket;
import java.io.*;
import java.util.*;
import view.ServerView;

/**
 * Class for handling communication with a Client.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 *
 */

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	private PrintStream out;
	private String clientname;
	private List<String> supportedfeatures = new ArrayList<String>();
	private Peer peer;
	
	/**
	 * Creates a new ClientHandler for the server.
	 * 
	 * @param server
	 * the main server
	 * 
	 * @param sock
	 * communication line with the client
	 */
	public ClientHandler(Server server, Socket sock) {
		this.server = server;
		this.sock = sock;
	}
	
	/**
	 * Gets the name of the Client.
	 * 
	 * @return name
	 */
	public String getClientName() {
		return clientname;
	}
	
	/**
	 * Gets the socket of this handler.
	 * 
	 * @return socket
	 */
	public Socket getSocket() {
		return sock;
	}
	
	/**
	 * Connects a client and confirms it with another method.
	 * 
	 * Gets the name from the client. Also gets the features and
	 * compares them with the features of the server. Remembers
	 * if there are corresponding features.
	 */
	protected void connectClient(String message) {
		try {
			Scanner scan = new Scanner(message);
			scan.skip("CONNECT");
			if (!scan.hasNext()){
				scan.close();
				throw new IOException("CONNECT command has no follow up.");
			}
			clientname = scan.next();
			String feature = "";
			while (scan.hasNext()) {
				feature = scan.next();
				if (server.getFeatures().contains(feature)) {
					supportedfeatures.add(feature);
				}
			}
			scan.close();
			connectionMade();
		} catch (IOException e) {
			sendError("ConnectionFailure", e.getMessage());
			e.printStackTrace();
		}
	}
	
	/**
	 * Confirms the connection made. Sends also the supported features.
	 */
	protected void connectionMade() {
		String outpackage = "OK ";
		for (String feature : supportedfeatures) {
			outpackage = outpackage + feature + " ";
		}
		out.println(outpackage);
		out.flush();
		ServerView.connected(clientname);
	}
	
	/**
	 * Sends the lobby to the Client.
	 */
	protected void sendLobby() {
		String lobby = "LOBBY ";
		for (ClientHandler client : server.getClients()) {
			lobby = lobby + client.getClientName() + " ";
		}
		out.println(lobby);
		out.flush();
	}
	
	/**
	 * Sends an error to the Client.
	 * 
	 * @param header
	 * header of the error
	 * 
	 * @param message
	 * error specification
	 */
	protected void sendError(String header, String message) {
		out.println("ERROR " + header + " " + message);
		out.flush();
	}
	
	/**
	 * Sends an invite to the opponent.
	 * 
	 * @param name
	 * Client his own name
	 * 
	 * @param width
	 * supported width
	 * 
	 * @param height
	 * supported height
	 */
	protected void sendInviteToOpp(String name, String width, String height) {
		for (ClientHandler handler : server.getClients()) {
			if (!handler.getClientName().equals(name)) {
				handler.sendInvite(clientname, width, height);
			}
		}
	}
	
	/**
	 * Sends an incoming invite to the client.
	 * 
	 * @param name
	 * opponent's name
	 * 
	 * @param width
	 * width of the board the opponent supports
	 * 
	 * @param height
	 * heigth of the board the opponent supports
	 */
	protected void sendInvite(String name, String width, String height) {
		out.println("INVITE " + name + " " + width + " " + height);
		out.flush();
	}
	
	/**
	 * 
	 * @param name
	 */
	protected void setupGame(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("ACCEPT");
		String opp = scan.next();
		for (ClientHandler handler : server.getClients()) {
			if (handler.getClientName().equals(opp)) {
				GameHandler game = new GameHandler(handler, this);
				game.run();
			}
		}
	}
	
	protected void sendDecline(String name) {
		out.println("DECLINE " + name);
		out.flush();
	}
	
	protected void sendGameStart(String p1, String p2) {
		out.println("START " + p1 + " " + p2);
		out.flush();
	}
	
	protected void sendGameEnd(String type, String winner){
		out.println("END " + type + " " + winner);
		out.flush();
	}
	
	protected void requestMove() {
		out.println("REQUEST");
		out.flush();
	}
	
	protected void moveOk(short player, short column, String playername) {
		out.println("MOVE " + player + " " + column + " " + playername);
		out.flush();
	}
	
	protected void sendBoard(byte[] board) {
		int width = 7;
		int height = 6;
		out.println("BOARD " + width + " " + height + " " + board);
		out.flush();
	}
	
	public void run() {
		try {
			peer = new Peer(this);
			Thread peerthread = new Thread(peer);
			peerthread.start();
			out = new PrintStream(sock.getOutputStream());
		} catch (IOException e){
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		while (true) {
			
		}
	}
	
}
