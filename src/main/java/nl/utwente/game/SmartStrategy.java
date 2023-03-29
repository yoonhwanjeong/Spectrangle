package nl.utwente.game;

import nl.utwente.game.Player.Move;
import nl.utwente.game.Tile.Location;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.IntStream;

/**
 * Strategy that determines move and tile to exchange using point calculations.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class SmartStrategy implements Strategy {
	
	// ------------------------- Queries ----------------------------
	
	@Override
	public String getName() {
		return "Smart";
	}

	@Override
	public Move determineMove(Board board, List<Tile> tiles) {
		Map<Move, Integer> moves = new HashMap<>();
		IntStream.range(0, Board.DIM * Board.DIM).filter(i -> board.isPlayableField(i))
				.forEach(i -> {
					tiles.stream().forEach(tile -> {
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
		Move move = moves.entrySet().stream()
				.sorted(Collections.reverseOrder(Entry.comparingByValue()))
				.map(Entry::getKey).findFirst().orElse(null);
		Tile tile = tiles.stream().filter(t -> t.equals(move.getTile())).findFirst().orElse(null);
		tile.setOrientation(move.getTile().getOrientation());
		return new Move(move.getRow(), move.getColumn(), tile);
	}

	@Override
	public Tile determineTileToExchange(List<Tile> tiles) {
		return tiles.stream().sorted().findFirst().orElse(null);
	}

}
