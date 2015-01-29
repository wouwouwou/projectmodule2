package view;

//TODO Check and implement chat feature

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
	
	private Client client;
	
	public ClientView(Client cli) {
		client = cli;
	}
	
	public String getClientName() {
		return StandardInput.getString("\n> What's your name? \n");
	}

	public String getIP() {
		return StandardInput.getString("\n> Insert the ip-address. \n");
	}

	public int getPort() {
		return StandardInput.readInt("\n> Insert the port. \n");
	}

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

	public void serverDisconnected() {
		System.out.println("The server disconnected!\n"
						+ "Please restart the program.\n");
	}

	public void invitesSended() {
		System.out
						.println("Invites sended to every member in the lobby.\n"
						+ "Waiting for a reaction, or an arbitrary but suitable invite.\n");
	}
	
	public void showHint(int hint) {
		System.out.println("Hint: " + hint + " is a possible move!\n");
	}

	public void showBoard(Board board) {
		System.out.println("\nCurrent game situation: \n\n" + board.toString()
						+ "\n");
	}

	public void showGameStart(Board board, String opp, int number) {
		System.out.println("\nYou started a game with " + opp);
		showBoard(board);
		System.out.println("You are player " + number + "\n");
	}

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

	public void printString(String string) {
		System.out.println(string);
	}

	public void connected() {
		System.out
				.println("\nYou succesfully made a connection with the server!\n");
	}
	
	public void run() {
		
	}
}
