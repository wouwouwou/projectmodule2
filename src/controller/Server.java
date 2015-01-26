package controller;

import java.io.IOException;
import java.net.UnknownHostException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;
import view.ServerView;

/**
 * Server for the ConnectFour game
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
	
	List<ClientHandler> getClients() {
		return clients;
	}
	
	public void showLobby() {
		String lobby = "";
		for (ClientHandler client : clients) {
			lobby = lobby + client.getClientName();
		}
		ServerView.showClients(lobby);
	}
	
	public void run() {
		try {
			Thread serverview = new Thread(view);
			serverview.setName("ServerView");
			serverview.start();
			ServerSocket serversock = new ServerSocket(4321);
			ServerView.isActive(InetAddress.getLocalHost().getHostAddress(), serversock.getLocalPort());
			while(true) {
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