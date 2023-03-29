package nl.utwente.game;

import nl.utwente.game.Tile.Location;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.UUID;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Player of Spectrangle game.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public abstract class Player implements Comparable<Player> {
	
	/**
	 * Move of player.
	 * @author Yoon Hwan Jeong & Jordi Weldink
	 */
	public static class Move {
		
		// ------------------------- Instance variables -------------
		
		private int row;
		private int column;
		private Tile tile;
		
		//@ private invariant row >= 0 && row < Board.DIM;
		//@ private invariant column >= -row && column <= row;
		//@ private invariant tile != null;
		
		// ------------------------- Constructors -------------------
		
		/**
		 * Constructs a <code>Move</code>.
		 * @param row row of move
		 * @param column column of move
		 * @param tile tile of move
		 */
		//@ requires row >= 0 && row < Board.DIM;
		//@ requires column >= -row && column <= row;
		//@ requires tile != null;
		//@ ensures getRow() == row;
		//@ ensures getColumn() == column;
		//@ ensures getTile() == tile;
		public Move(int row, int column, Tile tile) {
			this.row = row;
			this.column = column;
			this.tile = tile;
		}
		
		// ------------------------- Queries ------------------------
		
		/**
		 * Returns row of this <code>Move</code>.
		 * @return row of this move
		 */
		/*@ pure @*/
		public int getRow() {
			return row;
		}
		
		/**
		 * Returns column of this <code>Move</code>.
		 * @return column of this move
		 */
		/*@ pure @*/
		public int getColumn() {
			return column;
		}

		/**
		 * Returns index of this <code>Move</code>.
		 * @return index of this move
		 */
		/*@ pure @*/
		public int getIndex() {
			return row * row + row + column;
		}

		/**
		 * Returns <code>Tile</code> of this <code>Move</code>.
		 * @return tile of this move
		 */
		/*@ pure @*/
		public Tile getTile() {
			return tile;
		}
		
		/*@ pure @*/
		@Override
		public Move clone() {
			return new Move(row, column, tile.clone());
		}
		
		/*@ pure @*/
		@Override
		public String toString() {
			return tile + " " + row + " " + column + " " + tile.getOrientation();
		}
		
	}

	// ------------------------- Instance variables -----------------

	private UUID uuid;
	private String name;
	private List<Tile> tiles;
	private int point;
	
	/*@ private invariant uuid != null && this instanceof HumanPlayer ==>
						  uuid == UUID.nameUUIDFromBytes(name.getBytes());
	 */
	//@ private invariant name != null;
	//@ private invariant point >= 0;
	
	// ------------------------- Constructors -----------------------
	
	/**
	 * Constructs a <code>Player</code> with given name.
	 * @param name name of this player
	 */
	//@ requires name != null;
	public Player(String name) {
		uuid = this instanceof HumanPlayer ? UUID.nameUUIDFromBytes(name.getBytes())
				: UUID.randomUUID();
		this.name = name;
		tiles = new ArrayList<>();
		point = 0;
	}
	
	// ------------------------- Queries ----------------------------
	
	/**
	 * Returns <code>UUID</code> of this <code>Player</code>.
	 * @return uuid of this player
	 */
	/*@ pure @*/
	public UUID getUUID() {
		return uuid;
	}
	
	/**
	 * Returns name of this <code>Player</code>.
	 * @return name of this player
	 */
	/*@ pure @*/
	public String getName() {
		return name;
	}
	
	/**
	 * Returns tiles of this <code>Player</code>.
	 * @return tiles of this player
	 */
	/*@ pure @*/
	public List<Tile> getTiles() {
		return tiles;
	}
	
	/**
	 * Returns point of this <code>Player</code>.
	 * @return point of this player
	 */
	/*@ pure @*/
	public int getPoint() {
		return point;
	}
	
	/**
	 * Returns <tt>true</tt> if this <code>Player</code> has the specified <code>Tile</code>.
	 * @param tile tile whose presence in this player is to be tested
	 * @return <tt>true</tt> if this player has the specified tile
	 */
	/*@ pure @*/
	public boolean hasTile(Tile tile) {
		return tiles.contains(tile);
	}
	
	/**
	 * Returns <code>Tile</code> of given colors.
	 * If this <code>Player</code> does not have <code>Tile</code> of given colors,
	 * returns <code>null</code>.
	 * @param colors colors of tile
	 * @return tile of given colors
	 */
	//@ requires colors != null;
	/*@ pure @*/
	public Tile getTile(char[] colors, int pointOfTile) {
		return tiles.stream().filter(tile -> tile.equals(new Tile(colors, pointOfTile))).findFirst()
				.orElse(null);
	}
	
	/**
	 * Returns <code>Tile</code> of given colors.
	 * If this <code>Player</code> does not have <code>Tile</code> of given colors,
	 * returns <code>null</code>.
	 * @param tileString tile in [RYGBPW]{3}[1-6] format
	 * @return tile object from string
	 */
	//@ requires tileString != null && tileString.length() == 4;
	/*@ pure @*/
	public Tile getTile(String tileString) {
		return tiles.stream()
				.filter(tile -> tile.equals(new Tile(tileString.substring(0, 3).toCharArray(),
						Integer.parseInt(tileString.substring(3)))))
				.findFirst().orElse(null);
	}
	
	/**
	 * Returns <code>true</code> if this <code>Player</code> has
	 * at least one possible <code>Move</code> on given <code>Board</code>.
	 * @param board the current game board
	 * @return true if this player has at least one possible move on given board
	 */
	//@ requires board != null;
	/*@ pure @*/
	public boolean hasPossibleMoves(Board board) {
		return IntStream.range(0, Board.DIM * Board.DIM).filter(i -> {
			if (board.isPlayableField(i)) {
				Tile tile = tiles.stream().filter(t -> {
					Location orientation = Arrays.stream(Location.values()).filter(o -> {
						Tile clone = t.clone();
						clone.setOrientation(o);
						return board.isValidMove(i, clone);
					}).findFirst().orElse(null);
					return orientation != null;
				}).findFirst().orElse(null);
				return tile != null;
			} else {
				return false;
			}
		}).findFirst().orElse(-1) != -1;
	}
	
	/**
	 * Draws all tiles that this <code>Player</code> has.
	 * @return drawing of all tiles that this player has
	 */
	/*@ pure @*/
	public String drawAllTiles() {
		if (!tiles.isEmpty()) {
			List<String[]> drawings = tiles.stream().map(tile -> tile.draw().split("\n"))
					.collect(Collectors.toList());
			StringBuilder drawing = new StringBuilder();
			IntStream.range(0, drawings.get(0).length).forEach(i -> {
				drawings.stream().forEach(d -> {
					drawing.append(d[i]);
				});
				if (i < drawings.get(0).length - 1) {
					drawing.append("\n");
				}
			});
			return drawing.toString();
		} else {
			return "";
		}
	}
	
	/**
	 * Draws all orientations of given <code>Tile</code> that this <code>Player</code> has.
	 * @param tile tile that is to be drawn
	 * @return drawing of all orientations of given tile that this player has
	 */
	//@ requires hasTile(tile);
	/*@ pure @*/
	public String drawAllOrientations(Tile tile) {
		List<String[]> drawings = Arrays.stream(Location.values())
				.map(orientation -> tile.draw(orientation).split("\n"))
				.collect(Collectors.toList());
		StringBuilder drawing = new StringBuilder();
		IntStream.range(0, drawings.get(0).length).forEach(i -> {
			drawings.stream().forEach(d -> {
				drawing.append(d[i]);
			});
			if (i < drawings.get(0).length - 1) {
				drawing.append("\n");
			}
		});
		return drawing.toString();
	}
	
	/**
	 * Determines the next move.
	 * @param board the current game board
	 * @return the player's choice
	 */
	//@ requires board != null && hasPossibleMoves(board);
	//@ ensures board.isPlayableField(\result.getIndex());
	/*@ pure @*/
	public abstract Move determineMove(Board board);

	/**
	 * Determines the <code>Tile</code> to exchange.
	 * @return the tile to exchange
	 */
	//@ requires !getTiles().isEmpty();
	//@ ensures hasTile(\result);
	/*@ pure @*/
	public abstract Tile determineTileToExchange();

	/*@ pure @*/
	@Override
	public boolean equals(Object obj) {
		return obj instanceof Player && uuid.equals(((Player) obj).uuid);
	}
	
	/*@ pure @*/
	@Override
	public String toString() {
		return name + (this instanceof ComputerPlayer ? "[" + uuid + "]" : "");
	}
	
	/*@ pure @*/
	@Override
	public int compareTo(Player o) {
		return point != o.point ? Integer.compare(point, o.point) : uuid.compareTo(o.uuid);
	}
	
	// ------------------------- Commands ---------------------------
	
	/**
	 * Adds the specified <code>Tile</code> to this <code>Player</code>.
	 * @param tile tile to be added to this player
	 */
	//@ requires tile != null;
	public void addTile(Tile tile) {
		tiles.add(tile);
	}
	
	/**
	 * Removes the specified <code>Tile</code> from this <code>Player</code>.
	 * @param tile tile to be removed from this player
	 */
	//@ ensures !hasTile(tile);
	public void removeTile(Tile tile) {
		tiles.remove(tile);
	}
	
	/**
	 * Removes all <code>Tile</code>s.
	 */
	//@ ensures getTiles().isEmpty();
	public void clearTiles() {
		tiles.clear();
	}
	
	/**
	 * Adds point.
	 * @param calculatedPoint point to add
	 */
	public void addPoint(int calculatedPoint) {
		this.point += calculatedPoint;
	}
	
	/**
	 * Makes a move on the board.
	 * @param board the current board
	 * @param bag bag containing tiles
	 */
	//@ requires board != null && bag != null;
	public void makeMove(Board board, Bag bag) {
		Move move = determineMove(board);
		board.setField(move);
		removeTile(move.getTile());
		if (!bag.isEmpty()) {
			addTile(bag.getRandomTile());
		}
		point += board.calculateScore(move.getIndex());
	}
	
}
