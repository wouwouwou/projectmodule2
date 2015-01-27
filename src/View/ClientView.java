package view;

import java.util.Scanner;

import model.*;

/**
 * View for playing the game in Multiplayer mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class ClientView extends Thread {

	public static String getClientName() {
		return StandardInput.getString("\n> What's your name? \n");
	}

	public static String getIP() {
		return StandardInput.getString("\n> Insert the ip-address. \n");
	}

	public static int getPort() {
		return StandardInput.readInt("\n> Insert the port. \n");
	}

	public static void printGameEnd(String message) {
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

	public static void serverDisconnected() {
		System.out.println("The server disconnected!\n"
						+ "Please restart the program.\n");
	}

	public static void invitesSended() {
		System.out
						.println("Invites sended to every member in the lobby.\n"
						+ "Waiting for a reaction, or an arbitrary but suitable invite.\n");
	}
	
	public static void showHint(int hint) {
		System.out.println("Hint: " + hint + " is a possible move!\n");
	}

	public static void showBoard(Board board) {
		System.out.println("\nCurrent game situation: \n\n" + board.toString()
						+ "\n");
	}

	public static void showGameStart(Board board, String opp, int number) {
		System.out.println("\nYou started a game with " + opp);
		ClientView.showBoard(board);
		System.out.println("You are player " + number + "\n");
	}

	public static void printLobby(String lobby) {
		System.out.println("Current lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		System.out.println("____________________________________\n");
		scan.close();
	}

	public static void printError(String error) {
		System.out.println(error);
	}

	public static void printMessage(String message) {
		System.out.println(message);
	}

	public static void connected() {
		System.out
				.println("\nYou succesfully made a connection with the server!\n");
	}

}
