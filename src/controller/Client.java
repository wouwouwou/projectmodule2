package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.*;

import model.Board;
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
		out.flush();
		String response = in.readLine();
		if (response.startsWith("ACCEPT_CONNECT")) {
			ClientView.connected();
		}
	}
	
	private String getLobby() {
		out.println("REQUEST_LOBBY");
		out.flush();
		String res = null;
		try {
			res = in.readLine();
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
		return res;
	}
	
	private List<String> getClients(String lobby) {
		List<String> res = new ArrayList<String>();
		Scanner scan = new Scanner(lobby);
		scan.skip("LOBBY");
		while (scan.hasNext()) {
			res.add(scan.next());
		}
		scan.close();
		return res;
	}
	
	private boolean suitableInvite(String invite) {
		Scanner scan = new Scanner(invite);
		scan.skip("INVITE");
		int intwidth = 0;
		int intheight = 0;
		short shortwidth = 0;
		short shortheight = 0;
		if (scan.hasNextInt()) {
			intwidth = Integer.parseInt(scan.next());
			intheight = Integer.parseInt(scan.next());
		}
		else if (scan.hasNextShort()) {
			shortwidth = scan.nextShort();
			shortheight = scan.nextShort();
		}
		scan.close();
		return (intwidth == Board.WIDTH && intheight == Board.HEIGHT) || (shortwidth == Board.WIDTH && shortheight == Board.HEIGHT); 
	}
	
	private void getInvite() {
		String invite = null;
		while (true) {
			try {
				invite = in.readLine();
			} catch (IOException e) {
				System.out.println(e.getMessage());
				e.printStackTrace();
			}
			if (suitableInvite(invite)) {
				break;
			}
		}
		out.println("ACCEPT_INVITE");
		out.flush(); 
	}
	
	private void startGame() {
		String lobby = getLobby();
		ClientView.printLobby(lobby);
		List<String> clients = getClients(lobby);
		if (clients.size() == 1) {
			getInvite();
		}
		if (clients.size() >= 2) {
			
		}
	}
	
    public void run() {
    	try {
    		name = ClientView.getClientName();
    		sock = new Socket(InetAddress.getByName(ClientView.getIP()), 4321);
    		communicationSetup();
    		connectionSetup();
    		startGame();
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
