package nl.utwente.game;

import nl.utwente.game.Player.Move;
import nl.utwente.game.Tile.Location;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

/**
 * Strategy that determines move and tile to exchange randomly.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class NaiveStrategy implements Strategy {
	
	// ------------------------- Queries ----------------------------

	@Override
	public String getName() {
		return "Naive";
	}

	@Override
	public Move determineMove(Board board, List<Tile> tiles) {
		List<Move> moves = new ArrayList<>();
		IntStream.range(0, Board.DIM * Board.DIM).filter(i -> board.isPlayableField(i))
				.forEach(i -> {
					tiles.stream().forEach(tile -> {
						Arrays.stream(Location.values()).forEach(orientation -> {
							Tile clone = tile.clone();
							clone.setOrientation(orientation);
							if (board.isValidMove(i, clone)) {
								moves.add(new Move(board.getRow(i), board.getColumn(i), clone));
							}
						});
					});
				});
		Move move = moves.get((int) (Math.random() * moves.size()));
		Tile tile = tiles.stream().filter(t -> t.equals(move.getTile())).findFirst().orElse(null);
		tile.setOrientation(move.getTile().getOrientation());
		return new Move(move.getRow(), move.getColumn(), tile);
	}

	@Override
	public Tile determineTileToExchange(List<Tile> tiles) {
		return Math.random() < 0.2 ? null : tiles.get((int) (Math.random() * tiles.size()));
	}

}
