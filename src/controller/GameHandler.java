package controller;

import model.Board;
import model.Mark;
import java.util.Scanner;

public class GameHandler implements Runnable {
	
	// -- Instance variables -----------------------------------------

    public static final int NUMBER_PLAYERS = 2;

    /*@
       private invariant board != null;
     */
    /**
     * The board.
     */
    private Board board;
    
    private ClientHandler[] clients;
    
    /*@
       private invariant 0 <= current  && current < NUMBER_PLAYERS;
     */
    /**
     * Index of the current player.
     */
    private int current;

    // -- Constructors -----------------------------------------------

    /**
     * Creates a new LocalGame object.
     */
    public GameHandler(ClientHandler p1, ClientHandler p2) {
        board = new Board();
        clients = new ClientHandler[NUMBER_PLAYERS];
        clients[0] = p1;
        clients[1] = p2;
        current = 0;
    }

    // -- Commands ---------------------------------------------------
    
    public void run() {
    	clients[0].sendGameStart(clients[0].getClientName(), clients[1].getClientName());
		clients[1].sendGameStart(clients[0].getClientName(), clients[1].getClientName());
		play();
    }

    /**
     * Plays the Connect Four game. <br>
     * First the (still empty) board is shown. Then the game is played until it
     * is over. Players can make a move one after the other. After each move,
     * the changed game situation is printed.
     */
    private void play() {
    	clients[current].requestMove();
    }
    
    protected boolean checkMove(String message) {
    	int choice = determineMove(message);
        return board.isColumn(choice) && board.containsEmptyColumn(choice);
    }
    
    protected void move(String message) {
    	Scanner scan = new Scanner(message);
    	scan.skip("MOVE");
    	scan.next();
    	int choice = scan.nextInt();
    	scan.close();
    	if (current == 0) {
        	board.setField(board.determineField(choice), Mark.RED);
        }
        else {
        	board.setField(board.determineField(choice), Mark.BLU);
        }
    	clients[0].moveOk(message);
    	clients[1].moveOk(message);
        current = (current+1)%2;
        if(!board.hasWinner() && !board.isFull()) {
        	clients[current].requestMove();
        }
        else if (board.isWinner(Mark.RED)) {
        	clients[0].sendGameEnd("WIN", clients[0].getClientName());
        	clients[1].sendGameEnd("WIN", clients[0].getClientName());
        }
        else if (board.isWinner(Mark.BLU)) {
        	clients[0].sendGameEnd("WIN", clients[1].getClientName());
        	clients[1].sendGameEnd("WIN", clients[1].getClientName());
        }
        else if (board.isFull()) {
        	clients[0].sendGameEnd("DRAW", "Bord is vol!");
        	clients[1].sendGameEnd("DRAW", "Bord is vol!");
        }
    }
    
    private int determineMove(String message) {
    	Scanner scan = new Scanner(message);
    	scan.skip("MOVE");
    	if(scan.nextInt() == current + 1) {
    		int res = scan.nextInt();
    		scan.close();
    		return res;
    	}
    	scan.close();
    	return -1;
    	
    }
}
