package controller;

import model.Board;
import model.Player;
import view.StandardInput;

/**
 * Local controller class for the Connect Four game. 
 * 
 * @author Jan-Jaap van Raffe and Wouter Bos
 * @version v1.0
 */

public class LocalGame {

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

    /*@
      requires p0 != null;
      requires p1 != null;
     */
    /**
     * Creates a new Game object.
     * 
     * @param p0
     *            the first player
     * @param p1
     *            the second player
     */
    public LocalGame(Player p0, Player p1) {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = p0;
        players[1] = p1;
        current = 0;
    }

    // -- Commands ---------------------------------------------------

    /**
     * Starts the Connect Four game. <br>
     * Asks after each ended game if the user wants to continue.
     * Continues until the user doesn't want to play anymore.
     */
    public void start() {
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
        this.showBoard();
        do {
            players[current].makeMove(board);
            this.showBoard();
            current = (current+1)%2;
        } while (!board.hasWinner() && !board.isFull());
        this.printResult();
    }


    /**
     * Prints the game situation.
     */
    private void showBoard() {
        System.out.println("\nCurrent game situation: \n\n" + board.toString()
                + "\n");
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
