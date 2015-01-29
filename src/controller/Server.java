package controller;

//TODO Check

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
 * 
 */
public class Server extends Thread {

	private List<ClientHandler> clients = new ArrayList<ClientHandler>();
	private List<String> features = new ArrayList<String>();
	private ServerView view = new ServerView(this);

	private void addClient(ClientHandler client) {
		clients.add(client);
	}

	List<String> getFeatures() {
		return features;
	}

	public List<ClientHandler> getClients() {
		return clients;
	}

	synchronized void removeClient(String client) {
		Set<ClientHandler> s = new HashSet<ClientHandler>();
		for (ClientHandler handler : clients) {
			if (!handler.getClientName().equals(client)) {
				s.add(handler);
			}
		}
		clients.retainAll(s);
	}

	public void showLobby() {
		String lobby = "";
		for (ClientHandler client : clients) {
			lobby = lobby + " " + client.getClientName();
		}
		ServerView.showClients(lobby);
	}

	private ServerSocket setup() {
		ServerSocket res = null;
		try {
			res = new ServerSocket(
					StandardInput
							.readInt("\n> Insert the port number you want to use \n"));
		} catch (IOException e) {
			ServerView.printError("\nThis portnumber is already in use!");
		}
		return res;
	}

	public void run() {
		ServerSocket serversock = null;
		while (serversock == null) {
			serversock = setup();
		}
		try {
			Thread serverview = new Thread(view);
			serverview.setName("ServerView");
			serverview.start();
			ServerView.isActive(InetAddress.getLocalHost().getHostAddress(),
					  serversock.getLocalPort());
			while (true) {
				Socket sock = serversock.accept();
				ClientHandler handler = new ClientHandler(this, sock);
				handler.start();
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