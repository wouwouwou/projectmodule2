package controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

/**
 * Server for the ConnectFour game
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 * 
 */

public class Server extends Thread {
	
	private List<ClientHandler> clients = new ArrayList<ClientHandler>();
	
	private void addClient(ClientHandler client) {
		clients.add(client);
	}
	
	public void run() {
		try {
			ServerSocket serversock = new ServerSocket(4321);
			System.out.println("Server is active on port " + serversock.getLocalPort() + ". \n");
			System.out.println("Server hostname: " + serversock.getInetAddress().getHostName() + " | Server IP : " + serversock.getInetAddress().getHostAddress());
			while(true) {
				Socket sock = serversock.accept();
				ClientHandler handler = new ClientHandler(this, sock);
				handler.start();
				addClient(handler);
			}
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	
}
