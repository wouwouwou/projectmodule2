package controller;

import java.net.Socket;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	
	public ClientHandler(Server server, Socket sock) {
		this.server = server;
		this.sock = sock;
	}
	
	public void run() {
		System.out.println(sock.getLocalPort() + " connected");
		System.out.println(sock.getLocalAddress() + " connected");
		System.out.println(sock.getPort() + " connected");
		System.out.println(sock.isConnected() + " connected");
		System.out.println(sock.isBound() + " connected");
	}
	
}
