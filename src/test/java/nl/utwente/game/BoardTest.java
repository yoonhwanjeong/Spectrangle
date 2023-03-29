package nl.utwente.game;

import nl.utwente.game.Player.Move;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class BoardTest {
	
	private Board board;
	private int bonusField;
	private int validField;
	private int invalidField;

	@BeforeEach
	void setUp() throws Exception {
		board = new Board();
		bonusField = 34;
		validField = 35;
		invalidField = 36;
	}

	@Test
	void test() {
		// 35 is valid field index but 36 is not
		assertEquals(validField,
				board.index(board.getRow(validField), board.getColumn(validField)));
		assertEquals(-1, board.index(board.getRow(invalidField), board.getColumn(invalidField)));
		assertTrue(board.isField(board.getRow(validField), board.getColumn(validField)));
		assertFalse(board.isField(board.getRow(invalidField), board.getColumn(invalidField)));
		assertNotNull(board.getField(board.getRow(validField), board.getColumn(validField)));
		assertNull(board.getField(board.getRow(invalidField), board.getColumn(invalidField)));
		assertTrue(board.isEmptyField(board.getRow(validField), board.getColumn(validField)));
		assertFalse(board.isEmptyField(board.getRow(invalidField), board.getColumn(invalidField)));
		assertTrue(board.isPlayableField(board.getRow(validField), board.getColumn(validField)));
		assertFalse(board.isPlayableField(board.getRow(bonusField), board.getColumn(bonusField)));
		// Board is initially empty
		assertTrue(board.isEmpty());
		assertFalse(board.isFull());
		// First placed tile does not have matching sides
		Tile tile = new Tile(new char[] {Tile.RED, Tile.RED, Tile.RED}, 6);
		assertEquals(0, board.calculateEdges(0, tile));
		// First tile cannot be placed on bonus field
		Move move = new Move(board.getRow(bonusField), board.getColumn(bonusField), tile);
		assertFalse(board.isValidMove(move));
		move = new Move(board.getRow(validField), board.getColumn(validField), tile);
		// (Score) = (Point of tile) * max(1, Number of matching sides) * (Bonus)
		board.setField(move);
		assertEquals(tile.getPoint(), board.calculateScore(validField));
		// Deep copy of board has same data but different reference
		Board copy = board.deepCopy();
		assertFalse(board == copy);
		assertTrue(board.equals(copy));
		// Resetting board empties board
		assertFalse(board.isEmpty());
		board.reset();
		assertTrue(board.isEmpty());
	}

}
