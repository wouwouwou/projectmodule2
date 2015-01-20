package view;

import java.util.Scanner;

public class ServerView extends Thread {
	
	public void run() {
		String res;
		do {
			System.out.print("\nType EXIT to shut the server down. \n");
			Scanner in = new Scanner(System.in);
    		res = in.hasNextLine() ? in.nextLine() : null;
		} while (!res.equals("EXIT"));
	}
}
