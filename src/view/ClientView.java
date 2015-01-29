package view;

import java.util.Scanner;
import controller.Client;
import model.Board;

/**
 * View for playing the game in Multiplayer mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ClientView extends Thread {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant client != null;
	/**
	 * Corresponding client of this ClientView.
	 */
	private Client client;
	
	
	// -- Constructors -----------------------------------------------
	
	/**
	 * Creates a new ClientView.
	 * 
	 * @param cli
	 *            corresponding client
	 */
	public ClientView(Client cli) {
		client = cli;
	}
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns the corresponding client of this view.
	 * 
	 * @return view's corresponding client
	 */
	//@ pure
	public Client getClient() {
		return client;
	}
	
	/**
	 * Asks the Client for his name.
	 * 
	 * @return name of the client.
	 */
	public String getClientName() {
		return StandardInput.getString("\n> What's your name? \n");
	}
	
	/**
	 * Asks the Client for the IP-address he wants to connect to.
	 * 
	 * @return IP-address filled in by the client.
	 */
	public String getIP() {
		return StandardInput.getString("\n> Insert the ip-address. \n");
	}
	
	/**
	 * Asks the Client for the port he wants to connect to.
	 * 
	 * @return port filled in by the client.
	 */
	public int getPort() {
		return StandardInput.readInt("\n> Insert the port. \n");
	}
	
	/**
	 * When a game ends, prints the name of the winner, if there is one.
	 * Else, prints a message about the draw.
	 * 
	 * @param message
	 *            End game command from the server.
	 */
	public void printGameEnd(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("END");
		String wincondition = scan.next();
		if (wincondition.equals("WIN")) {
			System.out
							.println(scan.next() + " has won!\n\n");
		} else if (wincondition.equals("DRAW")) {
			System.out
							.println("The board is full, it is a draw!\n\n");
		} else {
			System.out
							.println("\nYour opponent left. You have won!\n\n");
		}
		scan.close();
	}
	
	/**
	 * Prints that the server has disconnected and that the Client has to start
	 * the program again.
	 */
	public void serverDisconnected() {
		System.out.println("The server disconnected!\n"
						+ "Please restart the program.\n");
	}

	/**
	 * Prints that the Server has send invites to everyone in the lobby.
	 * Also prints that the server waits for a reaction, or an arbitrary
	 * but suitable invite to accept.
	 */
	public void invitesSended() {
		System.out
						.println("Invites sended to every member in the lobby.\n"
						+ "Waiting for a reaction, or an arbitrary but suitable invite.\n");
	}

	/**
	 * Shows a hint for a move.
	 * 
	 * @param hint
	 *            the hint
	 */
	public void showHint(int hint) {
		System.out.println("Hint: " + hint + " is a possible move!\n");
	}
	
	/**
	 * Shows the current board.
	 * 
	 * @param board
	 *            the current board
	 */
	public void showBoard(Board board) {
		System.out.println("\nCurrent game situation: \n\n" + board.toString()
						+ "\n");
	}
	
	/**
	 * Prints the start of a game. First prints the opponent's name, then the
	 * board and last but not least, the player number of this client.
	 * 
	 * @param board
	 *            The board to print
	 * 
	 * @param opp
	 *            opponent's name
	 * 
	 * @param number
	 *            player number of this client
	 */
	public void showGameStart(Board board, String opp, int number) {
		System.out.println("\nYou started a game with " + opp);
		showBoard(board);
		System.out.println("You are player " + number + "\n");
	}
	
	/**
	 * Prints the current lobby of the server.
	 * 
	 * @param lobby
	 *            the lobby
	 */
	public void printLobby(String lobby) {
		System.out.println("Current lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		System.out.println("____________________________________\n");
		scan.close();
	}
	
	/**
	 * Prints an arbitrary String.
	 * 
	 * @param string
	 *            string to be printed
	 */
	public void printString(String string) {
		System.out.println(string);
	}
	
	/**
	 * Prints a successful-connection-message.
	 */
	public void connected() {
		System.out
				.println("\nYou succesfully made a connection with the server!\n");
	}
	
	/**
	 * Runs a ClientView thread. In this version, nothing is done with it.
	 * Program can be expanded by adding a chat feature. Then you need this method. :-)
	 */
	public void run() {
		
	}
}
