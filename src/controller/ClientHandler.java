package controller;

import java.net.Socket;
import java.io.*;

public class ClientHandler extends Thread {
	
	private Server server;
	private Socket sock;
	private BufferedReader in;
	private PrintStream out;
	
	public ClientHandler(Server server, Socket sock) {
		this.server = server;
		this.sock = sock;
	}
	
	public void run() {
		System.out.println(sock.getLocalPort());
		System.out.println(sock.getPort());
		try {
			in = new BufferedReader(new InputStreamReader((sock.getInputStream())));
			out = new PrintStream(sock.getOutputStream());
			System.out.println("\nWaiting for input.\n");
			System.out.println(in.readLine());
		} catch (IOException e){
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		while (true) {
			
		}
	}
	
}
