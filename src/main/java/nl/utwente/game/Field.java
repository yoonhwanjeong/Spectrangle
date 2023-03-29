package nl.utwente.game;

import java.util.Collections;
import java.util.Objects;

/**
 * Field of Spectrangle board.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class Field {
	
	private /*@ spec_public @*/ int row;
	private /*@ spec_public @*/ int column;
	private int bonus;
	private Tile tile;
	
	//@ public invariant row >= 0 && row < Board.DIM;
	//@ public invariant column >= -row && column <= row;
	/*@ private invariant bonus >= Collections.min(Board.BONUSES) &&
						  bonus <= Collections.max(Board.BONUSES);
	 */
	
	// ------------------------- Constructors -------------------------
	
	/**
	 * Constructs an empty <code>Field</code>.
	 * @param row row of this field
	 * @param column column of this field
	 * @param bonus bonus of this field
	 */
	//@ requires row >= 0 && row < Board.DIM;
	//@ requires column >= -row && column <= row;
	//@ requires bonus >= Collections.min(Board.BONUSES) && bonus <= Collections.max(Board.BONUSES);
	//@ ensures getTile() == null;
	public Field(int row, int column, int bonus) {
		this.row = row;
		this.column = column;
		this.bonus = bonus;
		tile = null;
	}
	
	// ------------------------- Queries -------------------------
	
	/**
	 * Returns row of this <code>Field</code>.
	 * @return row of this field
	 */
	/*@ pure @*/
	public int getRow() {
		return row;
	}

	/**
	 * Returns column of this <code>Field</code>.
	 * @return column of this field
	 */
	/*@ pure @*/
	public int getColumn() {
		return column;
	}

	/**
	 * Returns bonus of this <code>Field</code>.
	 * @return bonus of this field
	 */
	/*@ pure @*/
	public int getBonus() {
		return bonus;
	}
	
	/**
	 * Returns <code>Tile</code> of this <code>Field</code>.
	 * @return tile of this field
	 */
	/*@ pure @*/
	public Tile getTile() {
		return tile;
	}

	/**
	 * Returns <code>true</code> if this <code>Field</code> is facing upwards.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this field is facing upwards, otherwise, false
	 */
	//@ ensures \result == ((row + column) % 2 == 0);
	/*@ pure @*/
	public boolean isFacingUpwards() {
		return (row + column) % 2 == 0;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Field</code> has right neighbour.
	 * Otherwise, returns <code>false</code>
	 * @return true if this field has right neighbour, otherwise, false
	 */
	//@ ensures \result == (column + 1 <= row);
	/*@ pure @*/
	public boolean hasRightNeighbour() {
		return column + 1 <= row;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Field</code> has left neighbour.
	 * Otherwise, returns <code>false</code>
	 * @return true if this field has left neighbour, otherwise, false
	 */
	//@ ensures \result == (column - 1 >= -row);
	/*@ pure @*/
	public boolean hasLeftNeighbour() {
		return column - 1 >= -row;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Field</code> has other neighbour.
	 * Otherwise, returns <code>false</code>
	 * @return true if this field has other neighbour, otherwise, false
	 */
	//@ ensures \result == ((row + column) % 2 != 0) || (row + 1 < Board.DIM);
	/*@ pure @*/
	public boolean hasOtherNeighbour() {
		if (!isFacingUpwards()) {
			return (row + column) % 2 != 0;
		} else {
			return row + 1 < Board.DIM;
		}
	}
	
	/**
	 * Returns index of this <code>Field</code>.
	 * @return index of this field
	 */
	//@ ensures \result == row * row + row + column;
	/*@ pure @*/
	public int getIndex() {
		return row * row + row + column;
	}
	
	/**
	 * Returns index of right neighbour of this <code>Field</code> if it has one.
	 * Otherwise, returns -1.
	 * @return index of right neighbour of this field if it has one, otherwise, -1
	 */
	//@ ensures hasRightNeighbour() ==> \result == row * row + row + column + 1;
	/*@ pure @*/
	public int getRightNeighbourIndex() {
		if (hasRightNeighbour()) {
			return row * row + row + column + 1;
		} else {
			return -1;
		}
	}
	
	/**
	 * Returns index of left neighbour of this <code>Field</code> if it has one.
	 * Otherwise, returns -1.
	 * @return index of left neighbour of this field if it has one, otherwise, -1
	 */
	//@ ensures hasLeftNeighbour() ==> \result == row * row + row + column - 1;
	/*@ pure @*/
	public int getLeftNeighbourIndex() {
		if (hasLeftNeighbour()) {
			return row * row + row + column - 1;
		} else {
			return -1;
		}
	}
	
	/**
	 * Returns index of other neighbour of this <code>Field</code> if it has one.
	 * Otherwise, returns -1.
	 * @return index of other neighbour of this field if it has one, otherwise, -1
	 */
	/*@ ensures hasOtherNeighbour() ==> \result == (row - 1) * (row - 1) + row - 1 + column ||
										\result == (row + 1) * (row + 1) + row + 1 + column;
	 */
	/*@ pure @*/
	public int getOtherNeighbourIndex() {
		if (hasOtherNeighbour()) {
			if (!isFacingUpwards()) {
				return (row - 1) * (row - 1) + row - 1 + column;
			} else {
				return (row + 1) * (row + 1) + row + 1 + column;
			}
		} else {
			return -1;
		}
	}
	
	/**
	 * Returns <code>true</code> if this <code>Field</code> is empty.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this field is empty, otherwise, false
	 */
	//@ ensures \result == (getTile() == null);
	/*@ pure @*/
	public boolean isEmpty() {
		return tile == null;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Field</code> has bonus.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this field has bonus, otherwise, false
	 */
	//@ ensures \result == getBonus() > Collections.min(Board.BONUSES);
	/*@ pure @*/
	public boolean isBonus() {
		return bonus > Collections.min(Board.BONUSES);
	}
	
	/*@ pure @*/
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Field) {
			Field field = (Field) obj;
			return row == field.row && column == field.column && bonus == field.bonus
					&& Objects.equals(tile, field.tile);
		} else {
			return false;
		}
	}
	
	//@ also ensures \result != this && \result.equals(this);
	/*@ pure @*/
	@Override
	public Field clone() {
		Field field = new Field(row, column, bonus);
		field.setTile(tile != null ? tile.clone() : null);
		return field;
	}

	// ------------------------- Commands -------------------------

	/**
	 * Sets <code>Tile</code> of this <code>Field</code>.
	 * @param tile tile of this field
	 */
	//@ ensures getTile() == tile;
	public void setTile(Tile tile) {
		this.tile = tile;
	}
	
}
