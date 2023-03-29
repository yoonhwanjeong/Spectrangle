package nl.utwente.game;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Spectrangle game.
 * @author Jordi Weldink & Yoon Hwan Jeong
 */
public class Game {
	
	// ------------------------- Constants --------------------------
	
	public static final int MAX_TILES = 4;
	
	// ------------------------- Instance variables -----------------
	
	protected List<Player> players;
	protected Board board;
	protected Bag bag;
	protected Player currentPlayer;
	
	//@ protected invariant players.size() >= 2 && players.size() <= 4;
	
	// ------------------------- Constructors -----------------------
	
	/**
	 * Constructs <code>Game</code> with given <code>Player</code>s.
	 * @param players players playing this game
	 */
	//@ requires players != null && players.length >= 2 && players.length <= 4;
	public Game(Player... players) {
		this(Arrays.asList(players));
	}
	
	/**
	 * Constructs <code>Game</code> with given <code>Player</code>s.
	 * @param players players playing this game
	 */
	//@ requires players != null && players.size() >= 2 && players.size() <= 4;
	public Game(Collection<? extends Player> players) {
		this.players = players.stream().collect(Collectors.toList());
		board = new Board();
		bag = new Bag();
		currentPlayer = null;
	}
	
	// ------------------------- Queries ----------------------------
	
	/**
	 * Returns <code>List</code> of <code>Player</code>s.
	 * @return list of players
	 */
	/*@ pure @*/
	public List<Player> getPlayers() {
		return players;
	}
	
	/**
	 * Returns <code>Board</code> of <code>Game</code>.
	 * @return board of game
	 */
	/*@ pure @*/
	public Board getBoard() {
		return board;
	}
	
	/**
	 * Returns <code>Bag</code> of <code>Game</code>.
	 * @return bag of game
	 */
	/*@ pure @*/
	public Bag getBag() {
		return bag;
	}
	
	/**
	 * Returns current <code>Player</code>.
	 * @return current player
	 */
	/*@ pure @*/
	public Player getCurrentPlayer() {
		return currentPlayer;
	}
	
	/**
	 * Returns <code>true</code> if <code>Game</code> is over.
	 * @return true if game is over, otherwise, false
	 */
	/*@ pure @*/
	public boolean isOver() {
		return board.gameOver(bag, players);
	}
	
	/**
	 * Returns next <code>Player</code> playing after current <code>Player</code>.
	 * @param player current player
	 * @return next player playing after current player
	 */
	/*@ pure @*/
	public Player getNextPlayer(Player player) {
		return player == null ? players.get(0)
				: players.get((players.indexOf(player) + 1) % players.size());
	}
	
	// ------------------------- Commands ---------------------------
	
	/**
	 * Stars <code>Game</code>.
	 */
	public void start() {
		Collections.shuffle(players);
		players.stream().filter(player -> player instanceof SmartComputerPlayer)
				.forEach(player -> ((SmartComputerPlayer) player).setPlayers(players));
		IntStream.range(0, Game.MAX_TILES).forEach(i -> {
			players.stream().forEach(player -> {
				player.addTile(bag.getRandomTile());
			});
		});
		while (!isOver()) {
			currentPlayer = getNextPlayer(currentPlayer);
			System.out.println(board);
			players.stream().filter(player -> !player.equals(currentPlayer)).forEach(player -> {
				System.out.println(player + "'s tiles:");
				System.out.println(player.drawAllTiles());
			});
			System.out.println("Your tiles:");
			System.out.println(currentPlayer.drawAllTiles());
			if (currentPlayer.hasPossibleMoves(board)) {
				currentPlayer.makeMove(board, bag);
			} else {
				Tile tile = currentPlayer.determineTileToExchange();
				if (tile != null && !bag.isEmpty()) {
					currentPlayer.removeTile(tile);
					currentPlayer.addTile(bag.getRandomTile());
					bag.put(tile);
				}
			}
		}
		System.out.println(board);
		players.stream().sorted(Collections.reverseOrder()).forEach(player -> {
			System.out.print(player + " " + player.getPoint() + "\n");
		});
	}

	/**
	 * Main method for playing <code>Game</code> locally.
	 */
	public static void main(String[] args) {
//		Player p1 = new HumanPlayer("Jordi");
		Player p1 = new ComputerPlayer(new SmartStrategy());
//		Player p2 = new HumanPlayer("Yoon");
		Player p2 = new ComputerPlayer(new SmartStrategy());
//		Player p3 = new ComputerPlayer(new NaiveStrategy());
		Player p3 = new SmartComputerPlayer();
		Player p4 = new ComputerPlayer(new SmartStrategy());
		Game game = new Game(p1, p2, p3, p4);
		game.start();
	}

}
