package controller;

import model.Board;
import model.ClientPlayer;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.Mark;
import model.Player;
import view.LocalView;
import view.StandardInput;

public class GameHandler {
	
	// -- Instance variables -----------------------------------------

    public static final int NUMBER_PLAYERS = 2;

    /*@
       private invariant board != null;
     */
    /**
     * The board.
     */
    private Board board;

    /*@
       private invariant players.length == NUMBER_PLAYERS;
       private invariant (\forall int i; 0 <= i && i < NUMBER_PLAYERS; players[i] != null); 
     */
    /**
     * The 2 players of the game.
     */
    private Player[] players;

    /**
     * The 2 corresponding ClientHandlers.
     */
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
        players[0] = new ClientPlayer(p1, Mark.RED);
        players[1] = new ClientPlayer(p2, Mark.BLU);
        clients[0] = p1;
        clients[1] = p2;
        current = 0;
    }

    // -- Commands ---------------------------------------------------
    
    /**
     * Gets the players and starts a game.
     */
    public void run() {
    	startGame();
    }
    
    /**
     * Starts the Connect Four game. <br>
     * Asks after each ended game if the user wants to continue.
     * Continues until the user doesn't want to play anymore.
     */
    public void startGame() {
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
        do {
        	clients[current].requestMove();
        	try {
        	this.wait();
        	} catch (InterruptedException e) {
        		System.out.println(e.getMessage());
        		e.printStackTrace();
        	}
        } while (!board.hasWinner() && !board.isFull());
        this.printResult();
    }

    /*@
       requires this.board.gameOver();
     */
    /**
     * Prints the result of the last game. <br>
     */
    private void printResult() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMark()) ? players[0]
                    : players[1];
            System.out.println("Speler " + winner.getName() + " ("
                    + winner.getMark().toString() + ") has won!");
        } else {
            System.out.println("Draw. There is no winner!");
        }
    }
	
}
