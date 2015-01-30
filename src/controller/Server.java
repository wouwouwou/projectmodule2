package controller;

import java.io.IOException;
import java.net.UnknownHostException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

import view.ServerView;
import view.StandardInput;

/**
 * Server for the ConnectFour game.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class Server extends Thread {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant clients != null;
	/**
	 * A list of all connected clients.
	 */
	private List<ClientHandler> clients;
	
	//@ private invariant features != null;
	/**
	 * A list of all features the server supports.
	 */
	private List<String> features;
	
	//@ private invariant serverview != null;
	/**
	 * The view of this server.
	 */
	private ServerView serverview;
	
	//@ private invariant ssock != null;
	/**
	 * The ServerSocket.
	 */
	private ServerSocket ssock;
	
	
	// -- Constructors -----------------------------------------------
	
	/*@ ensures getFeatures() != null && getClients() != null &&
	 	getView() != null && getServerSocket() != null;
	 */
	/**
	 * Initializes a server.
	 * 
	 * @param args
	 *            the supported features
	 */
	public Server(String[] args) {
		clients = new ArrayList<ClientHandler>();
		features = new ArrayList<String>();
		if (args != null) {
			for (String feature : args) {
				addFeature(feature);
			}
		}
		serverview = new ServerView(this);
		while (ssock == null) {
			ssock = setupServerSocket();
		}
	}
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns a List with all features of this server.
	 * 
	 * @return features of the server.
	 */
	//@ pure
	public List<String> getFeatures() {
		return features;
	}
	
	/**
	 * Returns a List with all connected clients.
	 * 
	 * @return all connected clients
	 */
	//@ pure
	public List<ClientHandler> getClients() {
		return clients;
	}
	
	/**
	 * Returns the view of the server.
	 * 
	 * @return server's view
	 */
	//@ pure
	public ServerView getView() {
		return serverview;
	}
	
	/**
	 * Returns the ServerSocket of the server.
	 * 
	 * @return server's ServerSocket
	 */
	//@ pure
	public ServerSocket getServerSocket() {
		return ssock;
	}
	
	/**
	 * Shows the lobby in the ServerView.
	 */
	//@ pure
	public void showLobby() {
		String lobby = "";
		for (ClientHandler client : clients) {
			lobby = lobby + " " + client.getClientName();
		}
		serverview.showClients(lobby);
	}
	
	
	// -- Commands ---------------------------------------------------
	
	/*@ requires client != null;
	 	ensures \old(getClients()) != getClients() && getClients().contains(client);
	 */
	/**
	 * Adds a new client to the list of connected clients.
	 * 
	 * @param client
	 *            client to be added
	 */
	private void addClient(ClientHandler client) {
		clients.add(client);
	}
	
	//@ ensures \old(getClients()) != getClients() && !getClients().contains(client);
	/**
	 * Removes a client from the list of connected clients.
	 * 
	 * @param client
	 *            client to be removed
	 */
	synchronized void removeClient(String client) {
		Set<ClientHandler> s = new HashSet<ClientHandler>();
		for (ClientHandler handler : clients) {
			if (!handler.getClientName().equals(client)) {
				s.add(handler);
			}
		}
		clients.retainAll(s);
	}
	
	//@ ensures \old(getFeatures()) != getFeatures() && features.contains(feature);
	/**
	 * Adds a feature to the list of features.
	 * 
	 * @param feature
	 *            feature to be added
	 */
	private void addFeature(String feature) {
		features.add(feature);
	}
	
	/**
	 * Tries to make a new ServerSocket. If succeeded, returns it.
	 * Else prints an error.
	 * 
	 * @return ServerSocket if succeeded. Else null.
	 */
	private ServerSocket setupServerSocket() {
		ServerSocket res = null;
		try {
			res = new ServerSocket(
					StandardInput
							.readInt("\n> Insert the port number you want to use \n"));
		} catch (IOException e) {
			serverview.printString("\nThis portnumber is already in use!");
		}
		return res;
	}
	
	/**
	 * Runs the server and waits for clients to connect. If a client
	 * connects, makes a new ClientHandler and starts it as a thread.
	 * Also adds the ClientHandler to the list of connected clients.
	 */
	public void run() {
		try {
			Thread t = new Thread(serverview);
			t.start();
			serverview.isActive(InetAddress.getLocalHost().getHostAddress(),
					  ssock.getLocalPort());
			while (true) {
				Socket sock = ssock.accept();
				ClientHandler handler = new ClientHandler(this, sock);
				addClient(handler);
			}
		} catch (UnknownHostException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
}