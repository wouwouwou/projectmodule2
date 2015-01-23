package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Scanner;

/**
 * InvitePeer for recieving invites from the server.
 * 
 * @author  Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class Peer implements Runnable {

    protected BufferedReader in;

    /**
     * Constructor. creates a peer object based on the given parameters.
     * @param input
     * input from the socket
     */
    public Peer(Socket sock) throws IOException {
    	in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    }

    /**
     * Reads strings of the stream of the socket-connection and writes the characters to the default output
     */
    public void run() {
    	String bericht = null;
    	while (true) {
    		try {
    			bericht = in.readLine();
    			if (bericht.startsWith("GAME_START")) {
    				break;
    			}
    			if (bericht.startsWith("ACCEPT_INVITE")) {
    				break;
    			}
    		} catch (IOException e) {
    			break;
    		}
    		Scanner scan = new Scanner(bericht);
        	String command = scan.next();
        	switch (command) {
        	case "GAME_START":
        	case "ACCEPT_INVITE": 	break;
        	}
    	}
    }
}
