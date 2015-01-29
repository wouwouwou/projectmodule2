package controller;

import java.net.Socket;
import java.io.*;
import java.util.*;

/**
 * Class for handling communication with a Client.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ClientHandler implements Observer {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant server != null;
	/**
	 * The main server of this ClientHandler.
	 */
	private Server server;
	
	//@ private invariant socket != null;
	/**
	 * The socket of this handler.
	 */
	private Socket socket;
	
	//@ private invariant socket != null;
	/**
	 * The output of this handler.
	 */
	private PrintStream out;
	
	/**
	 * The name of the client this handler handles with.
	 */
	private String clientname;
	
	/**
	 * The list of features both the server and the client supports.
	 */
	private List<String> supportedfeatures;
	
	/**
	 * Peer thread for all incoming messages from the Client.
	 */
	private Thread peer;
	
	/**
	 * GameHandler for handling a game.
	 */
	private GameHandler game;
	
	/**
	 * The player number the client plays with.
	 */
	private int playernumber;
	
	
	// -- Constructors -----------------------------------------------
	
	/*@ ensures getServer() != null && getSocket() != null &&
		getPeer().isAlive() && getOutput() != null;
	 */
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
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Gets the name of the Client.
	 * 
	 * @return name
	 */
	//@ pure
	public String getClientName() {
		return clientname;
	}
	
	/**
	 * Gets the main server.
	 * 
	 * @return server
	 */
	//@ pure
	public Server getServer() {
		return server;
	}
	
	/**
	 * Gets the socket of this handler.
	 * 
	 * @return socket
	 */
	//@ pure
	public Socket getSocket() {
		return socket;
	}
	
	/**
	 * Gets the output of this handler.
	 * 
	 * @return handler's output
	 */
	//@ pure
	public PrintStream getOutput() {
		return out;
	}
	
	/**
	 * Gets the list of features supported by the server and the client.
	 * 
	 * @return supported feature list
	 */
	//@ pure
	public List<String> getFeatures() {
		return supportedfeatures;
	}
	
	/**
	 * Gets the peer thread of this handler.
	 * 
	 * @return handlers peer thread
	 */
	//@ pure
	public Thread getPeer() {
		return peer;
	}
	
	/**
	 * Gets the GameHandler this handler has to deal with.
	 * 
	 * @return Game Handler
	 */
	//@ pure
	public GameHandler getGameHandler() {
		return game;
	}
	
	/**
	 * Gets the player number of the client this handler deals with.
	 * 
	 * @return player number
	 */
	//@ pure
	public int getPlayerNumber() {
		return playernumber;
	}
	
	
	// -- Commands ---------------------------------------------------
	
	/*@ requires message.startsWith("CONNECT");
	 	ensures !\old(getClientName()).equals(getClientName()) &&
	 			!\old(getFeatures()).equals(getFeatures());
	 */
	/**
	 * Connects a client and confirms it with the connectionMade() method.
	 * 
	 * Gets the name from the client's message. Also gets the features and
	 * compares them with the features of the server. Remembers if there are
	 * corresponding features.
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
			supportedfeatures = new ArrayList<String>();
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
		server.getView().printString(outpackage);
		out.println(outpackage);
		out.flush();
		server.getView().connected(clientname);
	}

	/**
	 * Sends the lobby to the Client.
	 */
	protected void sendLobby() {
		String lobby = "LOBBY ";
		for (ClientHandler client : server.getClients()) {
			lobby = lobby + client.getClientName() + " ";
		}
		server.getView().printString(lobby);
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
		server.getView().printString(error);
		out.println(error);
		out.flush();
	}

	/**
	 * Sends an invite to the opponent.
	 * 
	 * @param name
	 *            Client's own name
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
	 * Sends an incoming invite (with board size) to the client.
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
		server.getView().printString(invite);
		out.println(invite);
		out.flush();
	}

	/**
	 * Sends an incoming invite (without board size) to the client.
	 * 
	 * @param name
	 *            opponent's name
	 */
	protected void sendInvite(String name) {
		String invite = "INVITE " + name;
		server.getView().printString(invite);
		out.println(invite);
		out.flush();
	}
	
	//@ ensures getGameHandler() != null && getGameHandler().countObservers() == 2;
	/**
	 * Sets up a game between two Client(handler)s. Fist skips the ACCEPT
	 * command from the client's message. Then makes a new GameHandler and
	 * assigns these to the two ClientHandlers. Also adds the Clienthandlers as
	 * observers to the Observable GameHandler. Then starts a new thread for the
	 * GameHandler.
	 * 
	 * @param message
	 *            the incoming ACCEPT message from the client.
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
	
	//@ requires arg != null;
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
	
	/*@ requires gamehandler != null;
	 	ensures getGameHandler().equals(gamehandler);
	 */
	/**
	 * Assigns a GameHandler to this ClientHandler.
	 * 
	 * @param gamehandler
	 *            the gamehandler to be assigned
	 */
	protected void setGameHandler(GameHandler gamehandler) {
		game = gamehandler;
	}
	
	//@ requires p1 != null && !p1.equals("") && p2 != null && !p2.equals("");
	/**
	 * Sends a Start Game message to the client.
	 * 
	 * @param p1
	 *            the name of player 1
	 * 
	 * @param p2
	 *            the name of player 2
	 */
	protected void sendGameStart(String p1, String p2) {
		if (p1.equals(clientname)) {
			playernumber = 1;
		} else {
			playernumber = 2;
		}
		String start = "START " + p1 + " " + p2;
		server.getView().printString(start);
		out.println(start);
		out.flush();
	}
	
	//@ requires type != null && !type.equals("") && winner != null && !winner.equals("");
	/**
	 * Sends a Game End message to the client.
	 * 
	 * @param type
	 *            type of game end
	 * 
	 * @param winner
	 *            the winner of the game
	 */
	protected void sendGameEnd(String type, String winner) {
		String end = "END " + type + " " + winner;
		server.getView().printString(end);
		game = null;
		out.println(end);
		out.flush();
	}
	
	/**
	 * Requests a move from the client.
	 */
	protected void requestMove() {
		server.getView().printString("REQUEST");
		out.println("REQUEST");
		out.flush();
	}
	
	//@ requires message != null && !message.equals("");
	/**
	 * Checks the move given by the client, if there exitst a GameHandler. If
	 * the move is a valid move, then passes it to the GameHandler. Otherwise
	 * requests another move.
	 * 
	 * @param message
	 *            move message sended by the client
	 */
	protected void checkMove(String message) {
		Scanner scan = new Scanner(message);
		String move = scan.next() + " " + playernumber + " " + scan.nextInt();
		scan.close();
		if (game == null) {
			sendError("GameError", "The game doesn't exist anymore.");
			server.getView().printString("The Game doesn't exist anymore");
		} else {
			boolean valid = game.checkMove(move);
			if (valid) {
				game.move(move);
			} else {
				requestMove();
			}
		}
	}
	
	//@ requires message != null && !message.equals("");
	/**
	 * Sends a confirmed move from the GameHandler to the Client.
	 * 
	 * @param message
	 *            the command for a confirmed move
	 */
	protected void moveOk(String message) {
		server.getView().printString(message);
		out.println(message);
		out.flush();
	}
	
	//@ requires message != null && !message.equals("");
	/**
	 * Prints an error message to the server's view.
	 * 
	 * @param message
	 *            the error message given by the client
	 */
	protected void printError(String message) {
		server.getView().printString(message);
	}
	
	//@ ensures getGameHandler() == null && !getServer().getClients().contains(getClientName());
	/**
	 * Handles the shutdown of the server. If there exists a game, disconnects
	 * the client from it and sets the game to null. Closes the output and
	 * removes the client from the server's list.
	 */
	public void serverShutDown() {
		if (game != null) {
			game.disconnect(clientname);
			game = null;
		}
		if (clientname != null) {
			out.close();
			server.removeClient(clientname);
		} else {
			server.removeClient(null);
		}
	}
	
	//@ ensures getGameHandler() == null && !getServer().getClients().contains(getClientName());
	/**
	 * Handles the shutdown of a client. If there exists a game, disconnects the
	 * client from it and sets the game to null. Closes the output and removes
	 * the client from the server's list. Shows also a message that the client
	 * has disconnected.
	 */
	public void clientShutDown() {
		if (game != null) {
			game.disconnect(clientname);
		}
		if (clientname != null) {
			server.getView().clientDisconnected(clientname);
			out.close();
			server.removeClient(clientname);
		} else {
			server.removeClient(null);
		}
	}
}
