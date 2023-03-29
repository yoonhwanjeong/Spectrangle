package nl.utwente.game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class FieldTest {
	
	private Field field0;
	private Field field1;
	private Field field2;
	private Field field3;

	@BeforeEach
	void setUp() throws Exception {
		field0 = new Field(0, 0, 1);
		field1 = new Field(1, -1, 1);
		field2 = new Field(1, 0, 3);
		field3 = new Field(1, 1, 1);
	}

	@Test
	void test() {
		assertEquals(0, field0.getRow());
		assertEquals(1, field1.getRow());
		assertEquals(1, field2.getRow());
		assertEquals(1, field3.getRow());
		assertEquals(0, field0.getColumn());
		assertEquals(-1, field1.getColumn());
		assertEquals(0, field2.getColumn());
		assertEquals(1, field3.getColumn());
		// Field index 2 is bonus field
		assertEquals(1, field0.getBonus());
		assertEquals(1, field1.getBonus());
		assertEquals(3, field2.getBonus());
		assertEquals(1, field3.getBonus());
		// Fields are initially empty
		assertNull(field0.getTile());
		assertNull(field1.getTile());
		assertNull(field2.getTile());
		assertNull(field3.getTile());
		Tile tile = new Tile(new char[] {Tile.RED, Tile.RED, Tile.RED}, 6);
		field0.setTile(tile);
		assertEquals(tile, field0.getTile());
		// Field index 0, 1, 3 are facing upwards, field index 2 is facing downwards
		assertTrue(field0.isFacingUpwards());
		assertTrue(field1.isFacingUpwards());
		assertFalse(field2.isFacingUpwards());
		assertTrue(field3.isFacingUpwards());
		// Field index 1, 2 have right neighbours, field index 0, 3 do not
		assertFalse(field0.hasRightNeighbour());
		assertTrue(field1.hasRightNeighbour());
		assertTrue(field2.hasRightNeighbour());
		assertFalse(field3.hasRightNeighbour());
		// Field index 2, 3 have left neighbours, field index 0, 1 do not
		assertFalse(field0.hasLeftNeighbour());
		assertFalse(field1.hasLeftNeighbour());
		assertTrue(field2.hasLeftNeighbour());
		assertTrue(field3.hasLeftNeighbour());
		// Field index 0, 1, 2, 3 have other neighbours
		assertTrue(field0.hasOtherNeighbour());
		assertTrue(field1.hasOtherNeighbour());
		assertTrue(field2.hasOtherNeighbour());
		assertTrue(field3.hasOtherNeighbour());
		assertEquals(0, field0.getIndex());
		assertEquals(1, field1.getIndex());
		assertEquals(2, field2.getIndex());
		assertEquals(3, field3.getIndex());
		assertEquals(-1, field0.getRightNeighbourIndex());
		assertEquals(2, field1.getRightNeighbourIndex());
		assertEquals(3, field2.getRightNeighbourIndex());
		assertEquals(-1, field3.getRightNeighbourIndex());
		assertEquals(-1, field0.getLeftNeighbourIndex());
		assertEquals(-1, field1.getLeftNeighbourIndex());
		assertEquals(1, field2.getLeftNeighbourIndex());
		assertEquals(2, field3.getLeftNeighbourIndex());
		assertEquals(2, field0.getOtherNeighbourIndex());
		assertEquals(5, field1.getOtherNeighbourIndex());
		assertEquals(0, field2.getOtherNeighbourIndex());
		assertEquals(7, field3.getOtherNeighbourIndex());
		// Tile of field index 0 is set above so is not empty
		assertFalse(field0.isEmpty());
		assertTrue(field1.isEmpty());
		assertTrue(field2.isEmpty());
		assertTrue(field3.isEmpty());
		// Field index 2 is bonus field
		assertFalse(field0.isBonus());
		assertFalse(field1.isBonus());
		assertTrue(field2.isBonus());
		assertFalse(field3.isBonus());
		// Clone has same data but different reference
		Field clone = field0.clone();
		assertFalse(field0 == clone);
		assertTrue(field0.equals(clone));
	}

}
