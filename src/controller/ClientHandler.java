package controller;

import java.net.Socket;
import java.io.*;
import java.util.*;
import view.ServerView;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	private BufferedReader in;
	private PrintStream out;
	private String clientname;
	private List<String> supportedfeatures = new ArrayList<String>();
	
	public ClientHandler(Server server, Socket sock) {
		this.server = server;
		this.sock = sock;
	}
	
	String getClientName() {
		return clientname;
	}
	
	private void connectClient() {
		try {
			String connectPackage;
			do {
				connectPackage = in.readLine();
			} while (!connectPackage.startsWith("CONNECT"));
			Scanner scan = new Scanner(connectPackage);
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
		} catch (IOException e) {
			out.println("ERROR Failed to connect to server. Reason: " + e.getMessage());
			out.flush();
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	private void connectionMade() {
		String outpackage = "ACCEPT_CONNECT ";
		for (String feature : supportedfeatures) {
			outpackage = outpackage + feature + " ";
		}
		out.println(outpackage);
		out.flush();
		ServerView.connected(clientname);
	}
	
	private void sendLobby() {
		try {
			String lobbyPackage;
			do {
				lobbyPackage = in.readLine();
			} while (!lobbyPackage.startsWith("REQUEST_LOBBY"));
			String lobby = "LOBBY ";
			for (ClientHandler client : server.getClients()) {
				lobby = lobby + client.getClientName() + " ";
			}
			out.println(lobby);
			out.flush();
		} catch (IOException e) {
			out.println("ERROR Failed to send the lobby.");
			out.flush();
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	public void run() {
		try {
			in = new BufferedReader(new InputStreamReader((sock.getInputStream())));
			out = new PrintStream(sock.getOutputStream());
			connectClient();
			connectionMade();
			sendLobby();
		} catch (IOException e){
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		while (true) {
			
		}
	}
	
}
