package nl.utwente.game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class BagTest {
	
	private Bag bag;

	@BeforeEach
	void setUp() throws Exception {
		bag = new Bag();
	}

	@Test
	void test() {
		// Bag has 36 tiles initially
		assertEquals(Board.DIM * Board.DIM, bag.size());
		assertFalse(bag.isEmpty());
		Tile tile = new Tile(new char[] {Tile.RED, Tile.RED, Tile.RED}, 6);
		assertTrue(bag.contains(tile));
		// Getting random tile removes tile from bag
		tile = bag.getRandomTile();
		assertFalse(bag.contains(tile));
		assertEquals(Board.DIM * Board.DIM - 1, bag.size());
		// Cloned bag has same tiles but different reference
		Bag clone = bag.clone();
		assertFalse(bag == clone);
		assertTrue(bag.equals(clone));
		// Putting tile into bag increases bag size by 1
		bag.put(tile);
		assertTrue(bag.contains(tile));
		assertEquals(Board.DIM * Board.DIM, bag.size());
	}

}
