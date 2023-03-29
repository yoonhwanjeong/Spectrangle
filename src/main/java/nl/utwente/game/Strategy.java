package nl.utwente.game;

import nl.utwente.game.Player.Move;

import java.util.List;

/**
 * Strategy that ComputerPlayer uses.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public interface Strategy {
	
	/**
	 * Returns name of this <code>Strategy</code>.
	 * @return name of this strategy
	 */
	String getName();
	
	/**
	 * Determines the next move.
	 * @param board the current game board
	 * @param tiles list of tiles
	 * @return next legal move
	 */
	Move determineMove(Board board, List<Tile> tiles);
	
	/**
	 * Determines the <code>Tile</code> to exchange.
	 * @param tiles list of tiles
	 * @return the tile to exchange
	 */
	Tile determineTileToExchange(List<Tile> tiles);
	
}
