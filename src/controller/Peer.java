package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Scanner;

/**
 * Peer for recieving messages
 * 
 * @author  Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class Peer implements Runnable {

    protected BufferedReader in;
    protected ClientHandler handler;
    protected Client client;
    
    /**
     * Constructor. Creates a peer object for a ClientHandler.
     * 
     * @param handler
     * the ClientHandler
     * 
     * @param sock
     * the socket of the ClientHandler
     */
    
    public Peer(ClientHandler handler) throws IOException {
    	this.handler = handler;
    	in = new BufferedReader(new InputStreamReader(handler.getSocket().getInputStream()));
    }
    
    /**
     * Constructor. Creates a peer object for a Client.
     * 
     * @param client
     * the Client
     * 
     * @param sock
     * the socket of the Client
     */
    public Peer(Client client) throws IOException {
    	this.client = client;
    	in = new BufferedReader(new InputStreamReader(client.getSocket().getInputStream()));
    }
    
    private void listenClient() {
    	while(true) {
    		String message = null;
    		try {
				message = in.readLine();
			} catch (IOException e) {
				e.printStackTrace();
			}
    		client.interrupt();
    		Scanner scan = new Scanner(message);
    		String command = scan.next();
    		switch(command) {
    		case "LOBBY": 	client.setLobby(message);
    						break;
    		case "INVITE": 	client.acceptInvite(message);
    						break;
    		case "START":	client.gameStart(message);
    						break;
    		}
    	}
    }
    
    private void listenHandler() {
    	while(true) {
    		String message = null;
    		try {
				message = in.readLine();
			} catch (IOException e) {
				e.printStackTrace();
			}
    		Scanner scan = new Scanner(message);
    		String command = scan.next();
    		switch(command) {
    		case "CONNECT":	handler.connectClient(message);
    						break;
    		case "INVITE": 	handler.sendInviteToOpp(scan.next(), scan.next(), scan.next());
    						break;
    		case "LOBBY":	handler.sendLobby();
    						break;
    		case "ACCEPT": 	handler.setupGame(message);
    						break;
    		}
    	}
    }

    public void run() {
    	if (client != null) {
    		listenClient();
    	}
    	if (handler != null) {
    		listenHandler();
    	}
    }
}
