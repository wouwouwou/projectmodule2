package controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

/**
 * Server for the ConnectFour game
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 * 
 */

public class Server extends Thread {
	
	private ServerSocket serversock;
	
	public void run() {
		try {
			serversock = new ServerSocket(4321);
			System.out.println("Server is active on port " + serversock.getLocalPort() + ". \n");
			
			Socket sock = serversock.accept();
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	
}
