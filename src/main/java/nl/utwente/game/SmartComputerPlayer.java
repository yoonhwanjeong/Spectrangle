package nl.utwente.game;

import nl.utwente.game.Tile.Location;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * ComputerPlayer that uses SmartStrategy and thinks one step ahead.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class SmartComputerPlayer extends ComputerPlayer {
	
	// ------------------------- Instance variables -----------------
	
	private List<Player> players;
	
	// ------------------------- Constructors -----------------------
	
	/**
	 * Constructs <code>SmartComputerPlayer</code> with default name and <code>SmartStrategy</code>.
	 */
	public SmartComputerPlayer() {
		super(new SmartStrategy().getName(), new SmartStrategy());
	}
	
	/**
	 * Constructs <code>SmartComputerPlayer</code> with given name and <code>SmartStrategy</code>.
	 * @param name name of smart computer player
	 */
	public SmartComputerPlayer(String name) {
		super(name, new SmartStrategy());
	}
	
	/**
	 * Constructs <code>SmartComputerPlayer</code> with given name and order of
	 * <code>Player</code>s.
	 * @param name    name of smart computer player
	 * @param players order of players
	 */
	public SmartComputerPlayer(String name, List<Player> players) {
		this(name);
		this.players = players;
	}
	
	// ------------------------- Queries ----------------------------
	
	/**
	 * Returns best <code>Move</code> by given <code>Player</code> at given <code>Board</code>.
	 * @param board board to get best move
	 * @param player player to make best move
	 * @return best move by given player at given board
	 */
	private Entry<Move, Integer> getBestMove(Board board, Player player) {
		Map<Move, Integer> moves = new HashMap<>();
		IntStream.range(0, Board.DIM * Board.DIM).filter(i -> board.isPlayableField(i))
				.forEach(i -> {
					player.getTiles().stream().forEach(tile -> {
						Arrays.stream(Location.values()).forEach(orientation -> {
							Tile clone = tile.clone();
							clone.setOrientation(orientation);
							if (board.isValidMove(i, clone)) {
								Board deepCopy = board.deepCopy();
								deepCopy.setField(i, clone);
								Move move = new Move(board.getRow(i), board.getColumn(i), clone);
								moves.put(move, deepCopy.calculateScore(i));
							}
						});
					});
				});
		return moves.entrySet().stream().sorted(Collections.reverseOrder(Entry.comparingByValue()))
				.findFirst().orElse(null);
	}

	@Override
	public Move determineMove(Board board) {
		Map<Move, Integer> moves = new HashMap<>();
		IntStream.range(0, Board.DIM * Board.DIM).filter(i -> board.isPlayableField(i))
				.forEach(i -> {
					getTiles().stream().forEach(tile -> {
						Arrays.stream(Location.values()).forEach(orientation -> {
							Tile clone = tile.clone();
							clone.setOrientation(orientation);
							if (board.isValidMove(i, clone)) {
								Board deepCopy = board.deepCopy();
								deepCopy.setField(i, clone);
								Move move = new Move(board.getRow(i), board.getColumn(i), clone);
								moves.put(move, deepCopy.calculateScore(i));
							}
						});
					});
				});
		Map<Board, Entry<Move, Integer>> boards = moves.entrySet().stream()
				.collect(Collectors.toMap(entry -> {
					Board copy = board.deepCopy();
					copy.setField(entry.getKey());
					return copy;
				}, entry -> entry));
		sortPlayers();
		players.stream().filter(player -> player != this).forEach(player -> {
			boards.entrySet().stream().forEach(entry -> {
				Entry<Move, Integer> bestMove = getBestMove(entry.getKey(), player);
				if (bestMove != null) {
					entry.getKey().setField(bestMove.getKey());
					entry.getValue().setValue(entry.getValue().getValue() - bestMove.getValue());
				}
			});
		});
		Entry<Move, Integer> move = boards.entrySet().stream()
				.collect(Collectors.toMap(entry -> entry.getValue().getKey(),
						entry -> entry.getValue().getValue()))
				.entrySet().stream().sorted(Collections.reverseOrder(Entry.comparingByValue()))
				.findFirst().orElse(null);
		return move != null ? move.getKey() : null;
	}
	
	// ------------------------- Commands ---------------------------

	/**
	 * Puts <code>SmartComputerPlayer</code> at index 0 and sorts other
	 * <code>Player</code>s by order.
	 */
	private void sortPlayers() {
		List<Player> varPlayers = new ArrayList<>();
		varPlayers.add(this);
		int i = players.indexOf(this);
		int j = (i + 1) % players.size();
		while (j != i) {
			varPlayers.add(players.get(j));
			j = (j + 1) % players.size();
		}
		players = varPlayers;
	}
	
	/**
	 * Sets order of <code>Player</code>s.
	 * @param players order of players
	 */
	public void setPlayers(List<Player> players) {
		this.players = players;
	}

}
