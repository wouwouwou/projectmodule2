package view;

import java.util.Scanner;

public class ServerView extends Thread {
	
	public static void isActive(String ip, int port) {
		System.out.println("Server is active on " + ip + ":" + port + ". \n");
	}
	
	public static void connected(String clientname) {
		System.out.println(clientname + " succesfully connected! \n");
	}
	
	public void run() {
		String res;
		do {
			System.out.print("\nType EXIT to shut the server down. \n");
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
		} while (!res.equals("EXIT"));
	}
}
