package view;

import java.util.*;
import controller.ClientHandler;
import controller.Server;

/**
 * View for a Server.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ServerView extends Thread {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant server != null;
	/**
	 * Corresponding server of this ServerView.
	 */
	private Server server;
	
	
	// -- Constructors -----------------------------------------------
	
	/**
	 * Creates a new ServerView.
	 * 
	 * @param serv
	 *            corresponding server
	 */
	public ServerView(Server serv) {
		server = serv;
	}
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns the corresponding server of this view.
	 * 
	 * @return view's corresponding server
	 */
	//@ pure
	public Server getServer() {
		return server;
	}
	
	
	// -- Commands ---------------------------------------------------
	
	/**
	 * Prints when a server is active. Also prints its IP-address and
	 * port-number.
	 * 
	 * @param ip
	 *            IP-address of the server
	 * 
	 * @param port
	 *            port number of the server
	 */
	public void isActive(String ip, int port) {
		System.out.println("Server is active on " + ip + ":" + port + " \n");
	}
	
	/**
	 * Prints a nice and beautiful message when a client connects.
	 * 
	 * @param name
	 *            name of the client
	 */
	public void connected(String name) {
		System.out.println(name + " succesfully connected!");
	}
	
	/**
	 * Prints a nicer and more beautiful message when a client disconnects.
	 * 
	 * @param name
	 *            name of the client
	 */
	public void clientDisconnected(String name) {
		System.out.println(name + " has disconnected!");
	}
	
	/**
	 * Shows the lobby of the server.
	 * 
	 * @param lobby
	 * the lobby
	 */
	public void showClients(String lobby) {
		System.out.println("\nCurrent lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		scan.close();
		System.out.println("____________________________________\n");
	}
	
	/**
	 * Prints an arbitrary and beautiful string.
	 * 
	 * @param string
	 *            the beautiful string
	 */
	public void printString(String string) {
		System.out.println(string);
	}
	
	/**
	 * Shows the commands of this server.
	 */
	private void showCommands() {
		System.out.println("\n-------------------------------------\n"
					 + "Type LOBBY to get a list of clients.\n"
				 	 + "Type EXIT to shut the server down. \n"
					 + "-------------------------------------\n");
	}
	
	/**
	 * Waits for input from the server's console (System.in).
	 * Only knows two commands: LOBBY and EXIT.
	 * LOBBY will show the lobby
	 * EXIT will terminate the system 
	 */
	public void run() {
		String res;
		showCommands();
		Scanner in;
		do {
			in = new Scanner(System.in);
			res = in.hasNextLine() ? in.nextLine() : null;
			if (res.equals("LOBBY")) {
				server.showLobby();
			} else if (!res.equals("EXIT")) {
				showCommands();
			}
		} while (!res.equals("EXIT"));
		in.close();
		Set<ClientHandler> set = new HashSet<ClientHandler>();
		for (ClientHandler client : server.getClients()) {
			set.add(client);
		}
		for (ClientHandler handler : set) {
			handler.serverShutDown();
		}
		System.out.println("\nServer disconnected.");
		System.exit(0);
	}
}
