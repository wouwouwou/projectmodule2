package view;

import java.util.Scanner;

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
	
	public static void printLobby(String lobby) {
		System.out.println("Current lobby:");
		System.out.println("____________________________________\n");
		Scanner scan = new Scanner(lobby);
		scan.skip("LOBBY");
		while (scan.hasNext()) {
			System.out.println(scan.next());
		}
		System.out.println("____________________________________\n");
	}
	
	public static void connected() {
		System.out.println("\nYou succesfully made a connection with the server!\n");
	}
	
}
