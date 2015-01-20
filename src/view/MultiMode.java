package view;

import java.net.Socket;
import java.net.InetAddress;

/**
 * View for playing the game in Multiplayer mode.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class MultiMode extends Thread {
	
	private Socket socket;
	
    public void run() {
    	try {
    		byte[] ip = new byte[4];
    		String[] stringip = StandardInput.getString("\n> Insert the ip-address.\n").split(".");
    		for (String ippart : stringip) {
    			
    		}
    		socket = new Socket(InetAddress.getByAddress(ip), 4321);
    		System.out.println(socket.getPort());
    		System.out.println(socket.getInetAddress());
    		System.out.println(socket.getLocalPort());
    		System.out.println(socket.isConnected());
    		while (true) {
    			
    		}
    	} catch (Exception e) {
    		System.out.println(e.getMessage());
    		e.printStackTrace();
    	}
    	
    }
}
