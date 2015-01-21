package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import view.ClientView;

public class Client extends Thread {
	
	private Socket sock;
	private String name;
	private PrintStream out;
	private BufferedReader in;
	
	private void communicationSetup() {
		try {
			in = new BufferedReader(new InputStreamReader((sock.getInputStream())));
			out = new PrintStream(sock.getOutputStream());
		} catch (IOException e){
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	private void connectionSetup() throws IOException {
		out.println("CONNECT " + name);
		String response = in.readLine();
		if (response.startsWith("ACCEPT_CONNECT")) {
			ClientView.connected();
		}
	}
	
	private void getLobby() {
		out.println("REQUEST_LOBBY");
		try {
			String lobby = in.readLine();
			ClientView.printLobby(lobby);
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
    public void run() {
    	try {
    		name = ClientView.getClientName();
    		sock = new Socket(InetAddress.getByName(ClientView.getIP()), 4321);
    		communicationSetup();
    		connectionSetup();
    		getLobby();
    		while (true) {
    			
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
