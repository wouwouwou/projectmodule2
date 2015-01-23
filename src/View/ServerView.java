package view;

import java.util.Scanner;
import controller.Server;

public class ServerView extends Thread {
	
	private Server server;
	
	public ServerView(Server server) {
		this.server = server;
	}
	
	public static void isActive(String ip, int port) {
		System.out.println("Server is active on " + ip + ":" + port + ". \n");
	}
	
	public static void connected(String clientname) {
		System.out.println(clientname + " succesfully connected! \n");
	}
	
	public static void showClients(String lobby) {
		System.out.println("\nCurrent lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		System.out.println("____________________________________\n");
	}
	
	private void showCommands() {
		System.out.println("-------------------------------------\n"
				+ "Type LOBBY to get a list of clients.\n"
				+ "Type EXIT to shut the server down. \n"
				+ "-------------------------------------");
	}
	
	public void run() {
		String res;
		showCommands();
		do {
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
    		if (res.equals("LOBBY")) {
    			server.showLobby();
    		}
    		else if (!res.equals("EXIT")) {
    			showCommands();
    		}
		} while (!res.equals("EXIT"));
		System.out.println("\nServer disconnected.");
		System.exit(0);
	}
}
