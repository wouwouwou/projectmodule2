package view;

import java.net.Socket;
import java.net.InetAddress;
import java.io.*;
import java.net.UnknownHostException;

/**
 * View for playing the game in Multiplayer mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class MultiMode extends Thread {
	
	private Socket sock;
	private String name;
	private PrintStream out;
	private BufferedReader in;
	
    public void run() {
    	try {
    		sock = new Socket(InetAddress.getByName(StandardInput.getString("\n> Insert the ip-address. \n")), 4321);
    		System.out.println(sock.getLocalPort());
    		System.out.println(sock.getPort());
    		try {
    			in = new BufferedReader(new InputStreamReader((sock.getInputStream())));
    			out = new PrintStream(sock.getOutputStream());
    			String bericht = StandardInput.getString("\nWhat's the message?\n");
    			out.println(bericht);
    		} catch (IOException e){
    			System.out.println(e.getMessage());
    			e.printStackTrace();
    		}
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
