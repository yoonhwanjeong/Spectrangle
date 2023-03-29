package nl.utwente.game;

import nl.utwente.game.Tile.Location;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TileTest {
	
	private Tile tile0;
	private Tile tile1;
	private Tile tile2;

	@BeforeEach
	void setUp() throws Exception {
		tile0 = new Tile(new char[] {Tile.RED, Tile.RED, Tile.RED}, 6);
		tile1 = new Tile(new char[] {Tile.RED, Tile.RED, Tile.YELLOW}, 5);
		tile2 = new Tile(new char[] {Tile.WHITE, Tile.WHITE, Tile.WHITE}, 1);
	}

	@Test
	void test() {
		assertEquals(Tile.RED, tile0.getColor(Location.RIGHT));
		assertEquals(Tile.RED, tile0.getColor(Location.OTHER));
		assertEquals(Tile.RED, tile0.getColor(Location.LEFT));
		assertEquals(Tile.RED, tile1.getColor(Location.RIGHT));
		assertEquals(Tile.RED, tile1.getColor(Location.OTHER));
		assertEquals(Tile.YELLOW, tile1.getColor(Location.LEFT));
		assertEquals(Tile.WHITE, tile2.getColor(Location.RIGHT));
		assertEquals(Tile.WHITE, tile2.getColor(Location.OTHER));
		assertEquals(Tile.WHITE, tile2.getColor(Location.LEFT));
		assertEquals("RRR", tile0.getColors());
		assertEquals("RRY", tile1.getColors());
		assertEquals("WWW", tile2.getColors());
		assertEquals(6, tile0.getPoint());
		assertEquals(5, tile1.getPoint());
		assertEquals(1, tile2.getPoint());
		// Tile is initially orientated to right but tile1 is orientated to other
		tile1.setOrientation(Location.OTHER);
		assertEquals(Location.RIGHT, tile0.getOrientation());
		assertEquals(Location.OTHER, tile1.getOrientation());
		assertEquals(Location.RIGHT, tile2.getOrientation());
		// Tile is initially facing upwards but tile1 is set to face downwards
		tile1.setFacingUpwards(false);
		assertTrue(tile0.isFacingUpwards());
		assertFalse(tile1.isFacingUpwards());
		assertTrue(tile2.isFacingUpwards());
		// tile2 is joker
		assertFalse(tile0.isJoker());
		assertFalse(tile1.isJoker());
		assertTrue(tile2.isJoker());
		// tile0 and tile1 match color at locations other and left
		assertFalse(tile0.matchColor(Location.RIGHT, tile1));
		assertTrue(tile0.matchColor(Location.OTHER, tile1));
		assertTrue(tile0.matchColor(Location.LEFT, tile1));
		// Clone has same data but different reference
		Tile clone = tile0.clone();
		assertFalse(tile0 == clone);
		assertTrue(tile0.equals(clone));
		// tile0 comes after tile1
		assertTrue(tile0.compareTo(tile1) > 0);
		// Resetting sets tile to face upwards and orientation to right
		tile1.reset();
		assertTrue(tile1.isFacingUpwards());
		assertEquals(Location.RIGHT, tile1.getOrientation());
	}

}
