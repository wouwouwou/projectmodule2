package controller;

//TODO JML

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

import model.Board;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.Mark;
import model.Player;
import view.ClientView;
import view.ConnectFour;
import view.StandardInput;

/**
 * Client class for the game Connect Four.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class Client extends Thread {

	// -- Instance variables -----------------------------------------

	/**
	 * The socket of this Client.
	 */
	private Socket sock;

	/**
	 * The name of the Client.
	 */
	private String clientname;

	/**
	 * PrintStream for writing messages to the Server.
	 */
	private PrintStream out;

	/**
	 * Peer for all incoming messages from the Server.
	 */
	private Peer peer;

	/**
	 * Field for keeping the most current version of the Server lobby.
	 */
	private String currentlobby;

	/**
	 * A board for showing the game status.
	 */
	private Board board;

	/**
	 * Player for knowing if the client is a human player of a computer player.
	 */
	private Player player;

	/**
	 * Boolean for tracking the ingame status of the client.
	 */
	private boolean ingame;

	// -- Queries ----------------------------------------------------
	/**
	 * Gets the socket of this Client.
	 * 
	 * @return the socket of the client.
	 */
	Socket getSocket() {
		return sock;
	}

	// -- Commands ---------------------------------------------------
	/**
	 * Sets up the input and the output from / to the socket. The input is
	 * temporary. Later on there will be a Peer handling it.
	 */
	private void communicationSetup() {
		try {
			out = new PrintStream(sock.getOutputStream());
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}

	/**
	 * Sends our name to the server for connection. Awaits a repsonse. If the
	 * response is right, the view will print that the connection is succesfull.
	 * Otherwise IOException or Error.
	 * 
	 * @throws IOException
	 */
	private void connectionSetup() throws IOException {
		out.println("CONNECT " + clientname);
		out.flush();
		BufferedReader in = new BufferedReader(new InputStreamReader(
				  sock.getInputStream()));
		String message = in.readLine();
		if (message.startsWith("OK")) {
			ClientView.connected();
		} else {
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
		Scanner scan = new Scanner(currentlobby);
		while (scan.hasNext()) {
			String lobbyname = scan.next();
			if (!lobbyname.equals(clientname)) {
				sendInvite(lobbyname);
			}
		}
		scan.close();
		ClientView.invitesSended();
	}

	/**
	 * Setsup a peer for incoming messages. Can throw an IOException when
	 * constructing the peer.
	 * 
	 * @throws IOException
	 */
	private void peerSetup() throws IOException {
		peer = new Peer(this);
		Thread peerthread = new Thread(peer);
		peerthread.setName(clientname + "-peer");
		peerthread.start();
	}

	/**
	 * Accepts every invite which comes in through the Peer, if the invite is
	 * suitable and the Client isn't in game. Otherwise declines the invite.
	 * 
	 * @param message
	 *            the incoming invite message
	 */
	void acceptInvite(String invite) {
		Scanner scan = new Scanner(invite);
		scan.skip("INVITE");
		String opp = scan.next();
		if (scan.hasNext()) {
			int width = Integer.parseInt(scan.next());
			int height = Integer.parseInt(scan.next());
			if (width == Board.WIDTH && height == Board.HEIGHT && !ingame) {
				out.println("ACCEPT " + opp);
				out.flush();
			}
		} else if (!ingame) {
			out.println("ACCEPT " + opp);
			out.flush();
		} else {
			out.println("DECLINE " + opp);
			out.flush();
		}
		scan.close();
	}

	/**
	 * Handles the Game-Start message from the server.
	 * 
	 * @param message
	 */
	void gameStart(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("START");
		String player1 = scan.next();
		String player2 = scan.next();
		int number = 1;
		String playertype = StandardInput
				  .readChoice("\n> Do you want to play yourself or "
						+ "should the computer play for you (s/c)?\n", "s", "c");
		if (player1.equals(clientname)) {
			board = new Board();
			if (playertype.equals("s")) {
				player = new HumanPlayer(clientname, Mark.RED);
			} else {
				player = new ComputerPlayer(Mark.RED);
			}
			ClientView.showGameStart(board, player2, number);
		} else {
			board = new Board();
			if (playertype.equals("s")) {
				player = new HumanPlayer(clientname, Mark.BLU);
			} else {
				player = new ComputerPlayer(Mark.BLU);
			}
			ClientView.showGameStart(board, player1, number + 1);
		}
		scan.close();
		ingame = true;
	}

	/**
	 * Handles receiving the lobby from the Server. Remembers it in a field,
	 * without showing it to the client.
	 * 
	 * @param lobby
	 *            the lobby from the server.
	 */
	void setLobby(String lobby) {
		Scanner scan = new Scanner(lobby);
		scan.skip("LOBBY");
		currentlobby = "";
		while (scan.hasNext()) {
			currentlobby = currentlobby + scan.next() + " ";
		}
		scan.close();
		ClientView.printLobby(currentlobby);
		try {
			boolean sendInvite = StandardInput
							.readBoolean(
							"> Do you want to send invites in everyone in the lobby (y/n)?\n",
							"y", "n");
			if (sendInvite) {
				sendInvites();
			} else {
				ClientView
				.printMessage("\nWaiting for an arbitrary but suitable invite.");
			}
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}

	/**
	 * Prints an error from the Server on the Standard Output.
	 * 
	 * @param error
	 *            The error message from the Server.
	 */
	void printError(String error) {
		Scanner scan = new Scanner(error);
		scan.skip("ERROR");
		ClientView.printError(scan.nextLine());
		scan.close();
	}

	/**
	 * Sends an invite to an opponent. Also sends the supporting width and
	 * height with the invite.
	 * 
	 * @param opp
	 *            the name of the opponent
	 */
	private void sendInvite(String opp) {
		int width = Board.WIDTH;
		int height = Board.HEIGHT;
		out.println("INVITE " + opp + " " + width + " " + height);
		out.flush();
	}

	/**
	 * Determines the move and sends it to the server.
	 */
	void sendMove() {
		Player computerplayer = new ComputerPlayer(player.getMark());
		int hint = computerplayer.determineMove(board);
		ClientView.showHint(hint);
		int column = player.determineMove(board);
		if (player instanceof ComputerPlayer) {
			try {
				Thread.sleep(1000);
			} catch (InterruptedException e) {
				System.out.println(e.getMessage());
				e.printStackTrace();
			}
		}
		String move = "MOVE " + column;
		out.println(move);
		out.flush();
	}

	/**
	 * Handles the MOVE command from the server. First does the move on the
	 * board, then shows the board.
	 * 
	 * @param move
	 *            the MOVE command
	 */
	void setMove(String move) {
		Scanner scan = new Scanner(move);
		scan.skip("MOVE");
		int playernumber = scan.nextInt();
		if (playernumber == 1) {
			board.setField(board.determineField(scan.nextInt()), Mark.RED);
		} else {
			board.setField(board.determineField(scan.nextInt()), Mark.BLU);
		}
		ClientView.showBoard(board);
		scan.close();
	}

	/**
	 * Handles the end of a game. Shows the type of ending and terminates the
	 * program.
	 * 
	 * @param message
	 *            The end-game message from the server
	 */
	void gameEnd(String message) {
		ClientView.printGameEnd(message);
		boolean nextmultigame = StandardInput.readBoolean("> Do you want to "
						+ "play another multiplayer game (y/n)?", "y", "n");
		if (nextmultigame) {
			requestLobby();
			board.reset();
			player = null;
			ingame = false;
		} else {
			System.exit(0);
		}
	}

	/**
	 * Handles a server shutdown. Shows a message and terminates the program.
	 */
	void serverShutDown() {
		ClientView.serverDisconnected();
		try {
			peer.in.close();
		} catch (IOException e) {
			System.out.println("Exception when closing the input"
							 + "at the Client Peer. " + e.getMessage());
			e.printStackTrace();
		}
		out.close();
		System.exit(0);
	}

	/**
	 * Asks the server for the lobby.
	 */
	private void requestLobby() {
		out.println("LOBBY");
		out.flush();
	}

	/**
	 * Sets up all communication with the server and asks if the client wants to
	 * send invites to everyone in the lobby. If yes, sends them. If no, waits
	 * for a suitable invite for a game.
	 */
	public void run() {
		try {
			clientname = ClientView.getClientName();
			this.setName(clientname);
			try {
				sock = new Socket(InetAddress.getByName(ClientView.getIP()),
						ClientView.getPort());
			} catch (IOException e) {
				ClientView.printError("\nFailed to connect to a server. "
								+ "Try running this program again.");
				System.exit(0);
			} catch (IllegalArgumentException e) {
				ClientView.printError("\nYou probably inserted a wrong portnumber. "
								+ "Try running this program again.");
				System.exit(0);
			}
			communicationSetup();
			connectionSetup();
			peerSetup();
			requestLobby();
		} catch (UnknownHostException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		} catch (IOException e) {
			System.out.println(e.getMessage());
			e.printStackTrace();
		}
	}
}
