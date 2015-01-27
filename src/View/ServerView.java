package view;

import java.util.*;
import controller.ClientHandler;
import controller.Server;

public class ServerView extends Thread {

	private Server server;

	public ServerView(Server serv) {
		this.server = serv;
	}

	public static void isActive(String ip, int port) {
		System.out.println("Server is active on " + ip + ":" + port + " \n");
	}

	public static void connected(String clientname) {
		System.out.println(clientname + " succesfully connected!");
	}

	public static void printError(String error) {
		System.out.println(error);
	}

	public static void clientDisconnected(String name) {
		System.out.println(name + " has disconnected!");
	}

	public static void showClients(String lobby) {
		System.out.println("\nCurrent lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		scan.close();
		System.out.println("____________________________________\n");
	}

	public static void printMessage(String message) {
		System.out.println(message);
	}

	private void showCommands() {
		System.out.println("\n-------------------------------------\n"
					 + "Type LOBBY to get a list of clients.\n"
				 	 + "Type EXIT to shut the server down. \n"
					 + "-------------------------------------\n");
	}

	public void run() {
		String res;
		showCommands();
		do {
			Scanner in = new Scanner(System.in);
			res = in.hasNextLine() ? in.nextLine() : null;
			if (res.equals("LOBBY")) {
				server.showLobby();
			} else if (!res.equals("EXIT")) {
				showCommands();
			}
		} while (!res.equals("EXIT"));
		Set<ClientHandler> set = new HashSet<ClientHandler>();
		for (ClientHandler client : server.getClients()) {
			set.add(client);
		}
		for (ClientHandler handler : set) {
			handler.shutDown();
		}
		System.out.println("\nServer disconnected.");
		
		System.exit(0);
	}
}
