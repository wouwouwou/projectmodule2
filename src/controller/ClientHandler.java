package controller;

//TODO Check, also make a method in the server class to get the serverview. Then implement the shit.

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

public class ClientHandler extends Thread implements Observer {

	private Server server;
	private Socket socket;
	private PrintStream out;
	private String clientname;
	private List<String> supportedfeatures = new ArrayList<String>();
	private Thread peer;
	private GameHandler game;
	private int playernumber;

	/**
	 * Creates a new ClientHandler for the server.
	 * 
	 * @param serv
	 *            the main server
	 * 
	 * @param sock
	 *            communication line with the client
	 */
	public ClientHandler(Server serv, Socket sock) {
		server = serv;
		socket = sock;
		try {
			Peer peertje = new Peer(this);
			peer = new Thread(peertje);
			peer.start();
			out = new PrintStream(socket.getOutputStream());
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
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
		return socket;
	}

	/**
	 * Connects a client and confirms it with another method.
	 * 
	 * Gets the name from the client. Also gets the features and compares them
	 * with the features of the server. Remembers if there are corresponding
	 * features.
	 */
	protected void connectClient(String message) {
		try {
			Scanner scan = new Scanner(message);
			scan.skip("CONNECT");
			if (!scan.hasNext()) {
				scan.close();
				throw new IOException("CONNECT command has no follow up.");
			}
			String name = scan.next();
			for (ClientHandler handler : server.getClients()) {
				if (name.equals(handler.clientname)) {
					scan.close();
					throw new IOException("There already exists a player with this name.");
				}
			}
			clientname = name;
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
			sendError("ConnectionFailure: ", e.getMessage());
			clientShutDown();
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
		ServerView.printMessage(outpackage);
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
		ServerView.printMessage(lobby);
		out.println(lobby);
		out.flush();
	}

	/**
	 * Sends an error to the Client.
	 * 
	 * @param header
	 *            header of the error
	 * 
	 * @param message
	 *            error specification
	 */
	protected void sendError(String header, String message) {
		String error = "ERROR " + header + " " + message;
		ServerView.printMessage(error);
		out.println(error);
		out.flush();
	}

	/**
	 * Sends an invite to the opponent.
	 * 
	 * @param name
	 *            Client his own name
	 * 
	 * @param width
	 *            supported width
	 * 
	 * @param height
	 *            supported height
	 */
	protected void sendInviteToOpp(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("INVITE");
		String name = scan.next();
		if (scan.hasNext()) {
			int width = scan.nextInt();
			int height = scan.nextInt();
			for (ClientHandler handler : server.getClients()) {
				if (handler.getClientName().equals(name)) {
					handler.sendInvite(clientname, width, height);
				}
			}
		} else {
			for (ClientHandler handler : server.getClients()) {
				if (handler.getClientName().equals(name)) {
					handler.sendInvite(clientname);
				}
			}
		}
		scan.close();
	}

	/**
	 * Sends an incoming invite to the client.
	 * 
	 * @param name
	 *            opponent's name
	 * 
	 * @param width
	 *            width of the board the opponent supports
	 * 
	 * @param height
	 *            heigth of the board the opponent supports
	 */
	protected void sendInvite(String name, int width, int height) {
		String invite = "INVITE " + name + " " + width + " " + height;
		ServerView.printMessage(invite);
		out.println(invite);
		out.flush();
	}

	/**
	 * Sends an incoming invite to the client.
	 * 
	 * @param name
	 *            opponent's name
	 * 
	 * @param width
	 *            width of the board the opponent supports
	 * 
	 * @param height
	 *            heigth of the board the opponent supports
	 */
	protected void sendInvite(String name) {
		String invite = "INVITE " + name;
		ServerView.printMessage(invite);
		out.println(invite);
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
				game = new GameHandler(handler, this);
				game.addObserver(this);
				game.addObserver(handler);
				handler.setGameHandler(game);
				Thread t = new Thread(game);
				t.start();
			}
		}
		scan.close();
	}

	/**
	 * This update is getting called when the Observable (the GameHandler) calls
	 * a notifyObservers(). Gets an argument form the GameHandler, which is a
	 * correct move. Sends it through to the method moveOk(String arg).
	 * 
	 * @param o
	 *            The Observable
	 * 
	 * @param arg
	 *            The argument which the Observable passes through.
	 */
	public void update(Observable o, Object arg) {
		if (arg instanceof String) {
			moveOk((String) arg);
		}
	}

	protected void setGameHandler(GameHandler gamehandler) {
		this.game = gamehandler;
	}

	protected void sendGameStart(String p1, String p2) {
		if (p1.equals(clientname)) {
			playernumber = 1;
		} else {
			playernumber = 2;
		}
		String start = "START " + p1 + " " + p2;
		ServerView.printMessage(start);
		out.println(start);
		out.flush();
	}

	protected void sendGameEnd(String type, String winner) {
		String end = "END " + type + " " + winner;
		ServerView.printMessage(end);
		game = null;
		out.println(end);
		out.flush();
	}

	protected void requestMove() {
		ServerView.printMessage("REQUEST");
		out.println("REQUEST");
		out.flush();
	}

	protected void checkMove(String message) {
		Scanner scan = new Scanner(message);
		String move = scan.next() + " " + playernumber + " " + scan.nextInt();
		scan.close();
		if (game == null) {
			sendError("GameError", "The game doesn't exist anymore.");
			ServerView.printError("The Game doesn't exist anymore");
		} else {
			boolean valid = game.checkMove(move);
			if (valid) {
				game.move(move);
			}
		}
	}

	protected void moveOk(String message) {
		ServerView.printMessage(message);
		out.println(message);
		out.flush();
	}

	protected void printError(String message) {
		ServerView.printError(message);
	}
	
	public void serverShutDown() {
		if (game != null) {
			game.disconnect(clientname);
		}
		if (clientname != null) {
			out.close();
			server.removeClient(clientname);
		} else {
			server.removeClient(null);
		}
		this.interrupt();
	}
	
	public void clientShutDown() {
		if (game != null) {
			game.disconnect(clientname);
		}
		if (clientname != null) {
			ServerView.clientDisconnected(clientname);
			out.close();
			server.removeClient(clientname);
		} else {
			server.removeClient(null);
		}
		this.interrupt();
	}

	/**
	 * Run method for starting this Thread. Sets up a Peer for incoming messages
	 * from the Client. Also sets up a PrintStream to send messages to the
	 * Client.
	 */
	public void run() {
		
	}
}
