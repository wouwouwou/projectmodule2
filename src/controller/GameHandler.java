package controller;

import model.Board;
import model.Mark;
import java.util.Scanner;
import java.util.Observable;

/**
 * Class for keeping a game between two client(handler)s.
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */
public class GameHandler extends Observable implements Runnable {
	
	
	// -- Instance variables -----------------------------------------
	
	//@ private invariant NUMBER_PLAYERS == 2;
	/**
	 * The amount of players.
	 */
	private static final int NUMBER_PLAYERS = 2;

	//@ private invariant board != null;
	/**
	 * The board.
	 */
	private Board board;
	
	/*@ private invariant clients.length == NUMBER_PLAYERS; private invariant
		(\forall int i; 0 <= i && i < NUMBER_PLAYERS; clients[i] != null);
	 */
	/**
	 * The Client(handler)s.
	 */
	private ClientHandler[] clients;

	//@ private invariant 0 <= current && current < NUMBER_PLAYERS;
	/**
	 * Index of the current player.
	 */
	private int current;
	
	
	// -- Constructors -----------------------------------------------

	/**
	 * Creates a new LocalGame object.
	 * 
	 * @param p1
	 *            name of first ClientHandler (player one)
	 * 
	 * @param p2
	 *            name of first ClientHandler (player one)
	 */
	public GameHandler(ClientHandler p1, ClientHandler p2) {
		board = new Board();
		clients = new ClientHandler[NUMBER_PLAYERS];
		clients[0] = p1;
		clients[1] = p2;
		current = 0;
	}
	
	
	// -- Queries ----------------------------------------------------
	
	/**
	 * Returns the board.
	 * 
	 * @return board
	 */
	//@ pure
	public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns the current player as integer.
	 * 
	 * @return integer of current player
	 */
	//@ pure
	public int getCurrent() {
		return current;
	}
	
	// -- Commands ---------------------------------------------------
	
	/**
	 * Plays the Connect Four game. First the handlers will send a Game-Start message
	 * to the clients. Then player one will be asked for a move.
	 */
	public void run() {
		clients[0].sendGameStart(clients[0].getClientName(),
				  clients[1].getClientName());
		clients[1].sendGameStart(clients[0].getClientName(),
				  clients[1].getClientName());
		clients[current].requestMove();
	}
	
	/*@ ensures \result == getBoard().isColumn(determineMove(message)) &&
		getBoard().containsEmptyColumn(determineMove(message));
	*/
	/**
	 * Checks if the move send by a client is a valid move.
	 * 
	 * @param message
	 *            Move command send by the client
	 * 
	 * @return true if it is a valid move
	 */
	boolean checkMove(String message) {
		int choice = determineMove(message);
		return board.isColumn(choice) && board.containsEmptyColumn(choice);
	}
	
	/**
	 * Handles an in game client who disconnects. Lets the other client win and
	 * sends a message to that client.
	 * 
	 * @param client
	 *            name of disconnected client
	 */
	void disconnect(String client) {
		if (clients[0].getClientName().equals(client)) {
			clients[1].sendGameEnd("DISCONNECT", clients[1].getClientName());
		} else {
			clients[0].sendGameEnd("DISCONNECT", clients[0].getClientName());
		}
	}
	
	/*@	requires checkMove(message);
	 	ensures !\old(getBoard()).equals(getBoard()) &&
	 	getCurrent() == (\old(getCurrent()) + 1) % 2;
	 */
	/**
	 * Does the move given by the client(handler). Checks if there is a winner.
	 * If so, sends a Game-End message to both client(handler)s. If not, asks
	 * the other client for a move.
	 * 
	 * @param message
	 *            the move message from the client
	 */
	void move(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("MOVE");
		scan.next();
		int choice = scan.nextInt();
		scan.close();
		if (current == 0) {
			board.setField(board.determineField(choice), Mark.RED);
		} else {
			board.setField(board.determineField(choice), Mark.BLU);
		}
		setChanged();
		notifyObservers(message);
		clearChanged();
		current = (current + 1) % 2;
		if (!board.hasWinner() && !board.isFull()) {
			clients[current].requestMove();
		} else if (board.isWinner(Mark.RED)) {
			clients[0].sendGameEnd("WIN", clients[0].getClientName());
			clients[1].sendGameEnd("WIN", clients[0].getClientName());
		} else if (board.isWinner(Mark.BLU)) {
			clients[0].sendGameEnd("WIN", clients[1].getClientName());
			clients[1].sendGameEnd("WIN", clients[1].getClientName());
		} else if (board.isFull()) {
			clients[0].sendGameEnd("DRAW", "Bord is vol!");
			clients[1].sendGameEnd("DRAW", "Bord is vol!");
		}
	}
	
	/*@ requires message != null && message.startsWith("MOVE");
	 	ensures \result >= -1;
	 */
	/**
	 * Gets the actual move as an integer out of the move-command send by the
	 * client. Returns -1 if the command is from the wrong client.
	 * 
	 * @param message
	 *            the move-command send by the client
	 * 
	 * @return the move as integer
	 */
	int determineMove(String message) {
		Scanner scan = new Scanner(message);
		scan.skip("MOVE");
		if (scan.nextInt() == current + 1) {
			int res = scan.nextInt();
			scan.close();
			return res;
		}
		scan.close();
		return -1;

	}
}
