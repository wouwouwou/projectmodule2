package controller;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import view.ClientView;

import java.util.Scanner;

import model.Board;

public class Client extends Thread {
	
	private Socket sock;
	private String clientname;
	private PrintStream out;
	private BufferedReader in;
	private Peer peer;
	private String currentlobby;
	private Board board;
	private boolean ingame;
	
	/**
	 * Gets the socket of this Client.
	 * 
	 * @return the socket of the client.
	 */
	public Socket getSocket() {
		return sock;
	}
	
	/**
	 * Sets the server up. Exception is thrown to the caller.
	 * 
	 * @throws IOException
	 */
	private void serverSetup() throws IOException {
		communicationSetup();
		connectionSetup();
		sendInvites();
		peerSetup();
	}
	
	/**
	 * Sets up the input and the output from / to the socket.
	 * Later on the input is handled by a peer.
	 */
	private void communicationSetup() {
		try {
			in = new BufferedReader(new InputStreamReader(sock.getInputStream()))
;			out = new PrintStream(sock.getOutputStream());
		} catch (IOException e){
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
	
	/**
	 * Sends our name to the server for connection.
	 * Awaits a repsonse. If the response is right,
	 * the view will print that the connection is succesfull.
	 * Otherwise IOException or Error.
	 * 
	 * @throws IOException
	 */
	private void connectionSetup() throws IOException {
			out.println("CONNECT " + clientname);
			out.flush();
			String message = in.readLine();
			if (message.startsWith("OK")) {
				ClientView.connected();
			}
			else {
				out.println("ERROR ConnectionFailure");
				out.flush();
				ClientView.printError("ERROR ConnectionFailure");
			}
	}
	
	/**
	 * Sends invites to everyone who is connected, except ourself.
	 * 
	 * @throws IOException
	 */
	private void sendInvites() throws IOException {
		requestLobby();
		setLobby(in.readLine());
		Scanner scan = new Scanner(currentlobby);
		while(scan.hasNext()) {
			String lobbyname = scan.next();
			if (!lobbyname.equals(clientname)) {
				sendInvite(lobbyname);
			}
		}
		scan.close();
		ClientView.invitesSended();
	}
	
	/**
	 * Setsup a peer for incoming messages.
	 * Can throw an IOException when constructing the peer.
	 * 
	 * @throws IOException
	 */
	private void peerSetup() throws IOException {
		peer = new Peer(this);
		Thread peerthread = new Thread(peer);
		peerthread.start();
	}
	
	/**
	 * Accepts every invite which comes in through the Peer, if
	 * the invite is suitable and the Client isn't in game.
	 * 
	 * @param message
	 * the accept-invite message
	 */
	protected void acceptInvite(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("INVITE");
		String opp = scan.next();
		int width = Integer.parseInt(scan.next());
		int height = Integer.parseInt(scan.next());
		if(width == Board.WIDTH && height == Board.HEIGHT && !ingame) {
			out.println("ACCEPT " + opp);
			out.flush();
		}
		else {
			sendError("AcceptInvite", "Couldn't accept invite!");
		}
		scan.close();
	}
	
	/**
	 * 
	 * @param message
	 */
	protected void gameStart(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("START");
		String player1 = scan.next();
		int number = 1;
		if (player1.equals(clientname)){
			ClientView.printStartGame(scan.next(), number);
		}
		else{
			ClientView.printStartGame(player1, number + 1);
		}
		scan.close();
		ingame = true;
	}
	
	protected void setLobby(String message) {
		Scanner scan = new Scanner (message);
		scan.skip("LOBBY");
		currentlobby = "";
		while (scan.hasNext()) {
			currentlobby = currentlobby + scan.next();
		}
		scan.close();
	}
	
	/**
	 * Sends an error message to the Server.
	 * 
	 * @param header
	 * header of the message 
	 * 
	 * @param message
	 * specified message
	 */
	protected void sendError(String header, String message) {
		out.println("ERROR " + header + " " + message);
		out.flush();
	}
	
	/**
	 * Sends an invite to an opponent.
	 * 
	 * @param opp
	 * the name of the opponent
	 */
	protected void sendInvite(String opp) {
		int width = Board.WIDTH;
		int height = Board.HEIGHT;
		out.println("INVITE " + opp + " " + width + " " + height);
		out.flush();
	}
	
	protected void sendMove() {
		String move = "MOVE";
		out.println(move);
		out.flush();
	}
	
	protected void shutDown() {
		out.println("QUIT");
		out.flush();
	}
	
	protected void requestBoard() {
		out.println("REQUEST");
		out.flush();
	}
	
	/**
	 * Asks the server for the lobby.
	 */
	protected void requestLobby() {
		out.println("LOBBY");
		out.flush();
	}
	
    public void run() {
    	try {
    		clientname = ClientView.getClientName();
    		sock = new Socket(InetAddress.getByName(ClientView.getIP()), 4321);
    		serverSetup();
    		while(true) {
    			
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
