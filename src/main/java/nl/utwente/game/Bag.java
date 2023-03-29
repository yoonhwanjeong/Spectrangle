package nl.utwente.game;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Bag that contains tiles of Spectrangle game.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class Bag {
	
	private /*@ spec_public @*/ List<Tile> tiles;
	
	// ------------------------- Constructors -------------------------
	
	/**
	 * Constructs a <code>Bag</code> that contains given tiles.
	 * @param tiles list of tiles that this bag contains
	 */
	//@ requires tiles != null;
	private Bag(List<Tile> tiles) {
		this.tiles = tiles;
	}
	
	/**
	 * Constructs a <code>Bag</code> with all 36 tiles.
	 */
	//@ ensures tiles.size() == Board.DIM * Board.DIM;
	public Bag() {
		tiles = new ArrayList<>();
		tiles.add(new Tile(new char[] {Tile.RED, Tile.RED, Tile.RED}, 6));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.BLUE, Tile.BLUE}, 6));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.GREEN, Tile.GREEN}, 6));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.YELLOW, Tile.YELLOW}, 6));
		tiles.add(new Tile(new char[] {Tile.PURPLE, Tile.PURPLE, Tile.PURPLE}, 6));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.RED, Tile.YELLOW}, 5));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.RED, Tile.PURPLE}, 5));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.BLUE, Tile.RED}, 5));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.BLUE, Tile.PURPLE}, 5));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.GREEN, Tile.RED}, 5));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.GREEN, Tile.BLUE}, 5));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.YELLOW, Tile.GREEN}, 5));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.YELLOW, Tile.BLUE}, 5));
		tiles.add(new Tile(new char[] {Tile.PURPLE, Tile.PURPLE, Tile.YELLOW}, 5));
		tiles.add(new Tile(new char[] {Tile.PURPLE, Tile.PURPLE, Tile.GREEN}, 5));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.RED, Tile.BLUE}, 4));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.RED, Tile.GREEN}, 4));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.BLUE, Tile.GREEN}, 4));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.BLUE, Tile.YELLOW}, 4));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.GREEN, Tile.YELLOW}, 4));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.GREEN, Tile.PURPLE}, 4));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.YELLOW, Tile.RED}, 4));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.YELLOW, Tile.PURPLE}, 4));
		tiles.add(new Tile(new char[] {Tile.PURPLE, Tile.PURPLE, Tile.RED}, 4));
		tiles.add(new Tile(new char[] {Tile.PURPLE, Tile.PURPLE, Tile.BLUE}, 4));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.BLUE, Tile.PURPLE}, 3));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.GREEN, Tile.YELLOW}, 3));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.GREEN, Tile.PURPLE}, 3));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.RED, Tile.BLUE}, 3));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.RED, Tile.PURPLE}, 2));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.PURPLE, Tile.RED}, 2));
		tiles.add(new Tile(new char[] {Tile.YELLOW, Tile.PURPLE, Tile.GREEN}, 2));
		tiles.add(new Tile(new char[] {Tile.GREEN, Tile.RED, Tile.PURPLE}, 1));
		tiles.add(new Tile(new char[] {Tile.BLUE, Tile.YELLOW, Tile.GREEN}, 1));
		tiles.add(new Tile(new char[] {Tile.RED, Tile.YELLOW, Tile.BLUE}, 1));
		tiles.add(new Tile(new char[] {Tile.WHITE, Tile.WHITE, Tile.WHITE}, 1));
	}
	
	// ------------------------- Queries -------------------------
	
	/**
	 * Returns the number of tiles in this <code>Bag</code>.
	 * @return the number of tiles in this bag
	 */
	/*@ pure @*/
	public int size() {
		return tiles.size();
	}
	
	/**
	 * Returns <tt>true</tt> if this <code>Bag</code> contains no tiles.
	 * @return <tt>true</tt> if this bag contains no tiles
	 */
	/*@ pure @*/
	public boolean isEmpty() {
		return tiles.isEmpty();
	}
	
	/**
	 * Returns <tt>true</tt> if this <code>Bag</code> contains the specified <code>Tile</code>.
	 * @param tile tile whose presence in this bag is to be tested
	 * @return <tt>true</tt> if this bag contains the specified tile
	 */
	/*@ pure @*/
	public boolean contains(Tile tile) {
		return tiles.contains(tile);
	}
	
	/**
	 * Returns a random <code>Tile</code> from this <code>Bag</code> and
	 * removes it from this <code>Bag</code>.
	 * If this <code>Bag</code> is empty, returns <code>null</code>.
	 * @return a random tile if this bag is not empty, otherwise, null
	 */
	//@ ensures !contains(\result);
	/*@ pure @*/
	public Tile getRandomTile() {
		if (!isEmpty()) {
			int index = (int) (Math.random() * tiles.size());
			Tile tile = tiles.get(index);
			tiles.remove(index);
			return tile;
		} else {
			return null;
		}
	}
	
	/*@ pure @*/
	@Override
	public boolean equals(Object obj) {
		return tiles.stream().filter(tile -> !((Bag) obj).contains(tile)).findFirst()
				.orElse(null) == null;
	}
	
	//@ also ensures \result != this && \result.equals(this);
	/*@ pure @*/
	@Override
	public Bag clone() {
		return new Bag(tiles.stream().map(Tile::clone).collect(Collectors.toList()));
	}
	
	// ------------------------- Commands -------------------------
	
	/**
	 * Puts the specified <code>Tile</code> to this <code>Bag</code>.
	 * @param tile tile to be put to this bag
	 */
	//@ requires tile != null;
	//@ ensures size() == \old(size()) + 1 && contains(tile);
	public void put(Tile tile) {
		tile.reset();
		tiles.add(tile);
	}
	
}
