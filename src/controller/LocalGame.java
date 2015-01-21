package controller;

import model.Board;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.Mark;
import model.Player;
import view.StandardInput;
import view.LocalMode;

/**
 * Local controller class for the Connect Four game. 
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class LocalGame implements Runnable{

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
    public LocalGame() {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        current = 0;
    }

    // -- Commands ---------------------------------------------------
    
    /**
     * Gets the players and starts a game.
     */
    public void run() {
    	getPlayers();
    	startGame();
    }
    
    //TODO JML
    /**
     * Gets the players.
     */
    private void getPlayers() {
    	String[] args = LocalMode.getPlayers();
    	
    	switch (args[0]) {
    	case "-N": 	players[0] = new ComputerPlayer(Mark.RED);
    //	case "-S": 	players[0] = new ComputerPlayer(Mark.RED);
    				break;		
    	default: 	players[0] = new HumanPlayer(args[0], Mark.RED);
    		
    	}
    	switch (args[1]) {
    	case "-N": 	players[1] = new ComputerPlayer(Mark.BLU);
    //	case "-S": 	players[1] = new ComputerPlayer(Mark.BLU);
    				break;
    	default: 	players[1] = new HumanPlayer(args[1], Mark.BLU);
    	}
    }
    
    /**
     * Starts the Connect Four game. <br>
     * Asks after each ended game if the user wants to continue.
     * Continues until the user doesn't want to play anymore.
     */
    public void startGame() {
        boolean doorgaan = true;
        while (doorgaan) {
            reset();
            play();
            doorgaan = StandardInput.readBoolean("\n> Play another time? (y/n)?", "y", "n");
        }
    }

    /**
     * Resets the game. <br>
     * The board is emptied and player[0] becomes the current player.
     */
    private void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Plays the Connect Four game. <br>
     * First the (still empty) board is shown. Then the game is played until it
     * is over. Players can make a move one after the other. After each move,
     * the changed game situation is printed.
     */
    private void play() {
        LocalMode.showBoard(board);
        do {
            players[current].makeMove(board);
            LocalMode.showBoard(board);
            current = (current+1)%2;
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
