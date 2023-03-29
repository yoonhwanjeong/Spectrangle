package nl.utwente.game;

import nl.utwente.game.Player.Move;
import nl.utwente.game.Tile.Location;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

/**
 * Board of Spectrangle game.
 * @author Jordi Weldink & Yoon Hwan Jeong
 */
public class Board {
	
	// ------------------------- Constants --------------------------

	public static final int DIM = 6; // 0-5
	public static final List<Integer> BONUSES = Arrays.asList(1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1,
			4, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 1);
	
	// ------------------------- Instance variables -----------------

	private Field[] fields; // contains 36 fields
	
	// ------------------------- Constructors -----------------------
	
	/**
	 * Constructs a <code>Board</code> with given fields.
	 * @param fields fields of this board
	 */
	//@ requires fields != null && fields.length == DIM * DIM;
	private Board(Field[] fields) {
		this.fields = fields;
	}

	/**
	 * Constructs an empty <code>Board</code>.
	 */
	//@ ensures isEmpty();
	public Board() {
		// create empty board, fields are set to be null when empty.
		// use the fields to update the lists
		fields = new Field[DIM * DIM];
		IntStream.range(0, DIM).forEach(i -> {
			IntStream.rangeClosed(-i, i).forEach(j -> {
				fields[index(i, j)] = new Field(i, j, BONUSES.get(index(i, j)));
			});
		});
	}

	// ------------------------- Queries ----------------------------
	
	/**
	 * Returns copy of this <code>Board</code>.
	 * @return copy of this board
	 */
	//@ ensures \result.equals(this) && \result != this;
	/*@ pure @*/
	public Board deepCopy() {
		return new Board(Arrays.stream(fields).map(Field::clone).toArray(Field[]::new));
	}

	/**
	 * Returns index corresponding to row and column.
	 * If row or column is invalid, returns -1.
	 * @param row row of index
	 * @param col column of index
	 * @return index corresponding to row and column or -1
	 */
	//@ ensures isField(\result);
	/*@ pure @*/
	public int index(int row, int col) {
    	if (row >= 0 && row < DIM && col >= -row && col <= row) {
    		return row * row + row + col;
    	} else {
    		return -1;
    	}
    }

	/**
	 * Returns row of index.
	 * If index is invalid, returns -1.
	 * @param index index whose row is to be found
	 * @return row of index or -1
	 */
	/*@ pure @*/
	public int getRow(int index) {
		return isField(index) ? fields[index].getRow() : -1;
	}

	/**
	 * Returns column of index.
	 * If index is invalid, returns -1.
	 * @param index index whose column is to be found
	 * @return column of index or -1
	 */
	/*@ pure @*/
	public int getColumn(int index) {
		return isField(index) ? fields[index].getColumn() : -DIM;
	}

	/**
	 * Returns <code>true</code> if index is valid.
	 * Otherwise, returns <code>false</code>.
	 * @param index index whose validness is to be tested
	 * @return true if index is valid, otherwise, false
	 */
	/*@ pure @*/
	public boolean isField(int index) {
		return index >= 0 && index < DIM * DIM;
	}

	/**
	 * Returns <code>true</code> if index is valid.
	 * Otherwise, returns <code>false</code>.
	 * @param row row of index
	 * @param col column of index
	 * @return true if index is valid, otherwise, false
	 */
	/*@ pure @*/
	public boolean isField(int row, int col) {
		return isField(index(row, col));
	}

	/**
	 * Returns <code>Field</code> at given index.
	 * If index is invalid, returns <code>null</code>.
	 * @param index index of field
	 * @return field at given index or null
	 */
	/*@ pure @*/
	public Field getField(int index) {
		return isField(index) ? fields[index] : null;
	}

	/**
	 * Returns <code>Field</code> at given index.
	 * If index is invalid, returns <code>null</code>.
	 * @param row row of index
	 * @param col column of index
	 * @return field at given index or null
	 */
	/*@ pure @*/
	public Field getField(int row, int col) {
		return getField(index(row, col));
	}

	/**
	 * Returns <code>true</code> if <code>Field</code> at given index is empty.
	 * Otherwise, returns <code>false</code>.
	 * @param index index of field whose emptiness to be tested
	 * @return true if field at given index is empty, otherwise, false
	 */
	/*@ pure @*/
	public boolean isEmptyField(int index) {
		return isField(index) && getField(index).isEmpty();
	}

	/**
	 * Returns <code>true</code> if <code>Field</code> at given index is empty.
	 * Otherwise, returns <code>false</code>.
	 * @param row row of index
	 * @param column column of index
	 * @return true if field at given index is empty, otherwise, false
	 */
	/*@ pure @*/
	public boolean isEmptyField(int row, int column) {
		return isEmptyField(index(row, column));
	}
	
	/**
	 * Returns <code>true</code> if <code>Field</code> at given index is playable.
	 * Otherwise, returns false.
	 * @param index index of field
	 * @return true if field at given index is playable, otherwise, false
	 */
	/*@ pure @*/
	public boolean isPlayableField(int index) {
		if (isEmpty() && !getField(index).isBonus()) {
			return true;
		} else if (isEmptyField(index)) {
			Field field = getField(index);
			boolean hasRightNeighbour = field.hasRightNeighbour()
					&& !isEmptyField(field.getRightNeighbourIndex());
			boolean hasLeftNeighbour = field.hasLeftNeighbour()
					&& !isEmptyField(field.getLeftNeighbourIndex());
			boolean hasOtherNeighbour = field.hasOtherNeighbour()
					&& !isEmptyField(field.getOtherNeighbourIndex());
			return hasRightNeighbour || hasLeftNeighbour || hasOtherNeighbour;
		} else {
			return false;
		}
	}
	
	/**
	 * Returns <code>true</code> if <code>Field</code> at index corresponding to
	 * given row and column is playable.
	 * Otherwise, returns false.
	 * @param row row of index
	 * @param column column of index
	 * @return true if field at given index is playable, otherwise, false
	 */
	/*@ pure @*/
	public boolean isPlayableField(int row, int column) {
		return isPlayableField(index(row, column));
	}
	
	/**
	 * Returns <code>true</code> if this <code>Board</code> is empty.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this board is empty, otherwise, false
	 */
	/*@ pure @*/
	public boolean isEmpty() {
		return IntStream.range(0, DIM * DIM).filter(i -> !isEmptyField(i)).findFirst()
				.orElse(-1) == -1;
	}

	/**
	 * Returns <code>true</code> if this <code>Board</code> is full.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this board is full, otherwise, false
	 */
	/*@ pure @*/
	public boolean isFull() {
		return IntStream.range(0, DIM * DIM).filter(i -> isEmptyField(i)).findFirst()
				.orElse(-1) == -1;
	}
	
	/**
	 * Returns number of matching sides as if given <code>Tile</code> is placed at index.
	 * If index is not valid or <code>Tile</code> is <code>null</code>, returns -1.
	 * @param index index where tile is placed
	 * @param tile placed tile
	 * @return number of matching sides or -1
	 */
	/*@ pure @*/
	public int calculateEdges(int index, Tile tile) {
		if (isField(index) && tile != null) {
			int numberOfNeighbours = 0;
			int numberOfMatchingSides = 0;
			Field field = getField(index);
			Tile clone = tile.clone();
			clone.setFacingUpwards(field.isFacingUpwards());
			if (field.hasRightNeighbour() && !getField(field.getRightNeighbourIndex()).isEmpty()) {
				numberOfNeighbours++;
				Field neighbourField = getField(field.getRightNeighbourIndex());
				Tile neighbourTile = neighbourField.getTile();
				if (clone.matchColor(Location.RIGHT, neighbourTile)) {
					numberOfMatchingSides++;
				}
			}
			if (field.hasLeftNeighbour() && !getField(field.getLeftNeighbourIndex()).isEmpty()) {
				numberOfNeighbours++;
				Field neighbourField = getField(field.getLeftNeighbourIndex());
				Tile neighbourTile = neighbourField.getTile();
				if (clone.matchColor(Location.LEFT, neighbourTile)) {
					numberOfMatchingSides++;
				}
			}
			if (field.hasOtherNeighbour() && !getField(field.getOtherNeighbourIndex()).isEmpty()) {
				numberOfNeighbours++;
				Field neighbourField = getField(field.getOtherNeighbourIndex());
				Tile neighbourTile = neighbourField.getTile();
				if (clone.matchColor(Location.OTHER, neighbourTile)) {
					numberOfMatchingSides++;
				}
			}
			return numberOfNeighbours == numberOfMatchingSides ? numberOfMatchingSides : 0;
		} else {
			return -1;
		}
	}

	/**
	 * Returns <code>true</code> if placing <code>Tile</code> at index is valid.
	 * Otherwise, returns <code>false</code>.
	 * @param index index where tile is to be placed
	 * @param tile tile to be placed
	 * @return true if placing tile at index is valid, otherwise, false
	 */
	/*@ pure @*/
	public boolean isValidMove(int index, Tile tile) {
		if (isPlayableField(index) && tile != null) {
			if (isEmpty()) { //first move has to be made
				return !getField(index).isBonus();
			} else { //normal move
				return calculateEdges(index, tile) > 0;
			}
		} else {
			return false;
		}
	}
	
	/**
	 * Returns <code>true</code> if <code>Move</code> is valid.
	 * Otherwise, returns <code>false</code>.
	 * @param move move to make
	 * @return true if move is valid, otherwise, false
	 */
	/*@ pure @*/
	public boolean isValidMove(Move move) {
		return move != null && isValidMove(move.getIndex(), move.getTile());
	}

	/**
	 * Calculates score at given index.
	 * @param index index where score is calculated
	 * @return score at given index
	 */
	/*@ pure @*/
	public int calculateScore(int index) { // not good yet
		if (!isField(index)) {
			return 0;
		} else {
			Field field = getField(index);
			Tile tile = field.getTile();
			return tile.getPoint() * Math.max(1, calculateEdges(index, tile)) * field.getBonus();
		}
	}

	/**
	 * Returns <code>true</code> if game is over.
	 * Otherwise, returns <code>false</code>.
	 * @param bag the bag of tiles
	 * @param players the list of players
	 * @return true if game is over, otherwise, false
	 */
	/*@ pure @*/
	public boolean gameOver(Bag bag, List<? extends Player> players) {
		return bag.isEmpty() && players.stream().filter(player -> player.hasPossibleMoves(this))
				.findFirst().orElse(null) == null;
	}

	/*@ pure @*/
	@Override
	public boolean equals(Object obj) {
		return obj instanceof Board && Arrays.equals(fields, ((Board) obj).fields);
	}

	/*@ pure @*/
	@Override
	public String toString() {
		List<Integer> values = new ArrayList<>();
		List<Character> vertical = new ArrayList<>();
		List<Character> left = new ArrayList<>();
		List<Character> right = new ArrayList<>();
		IntStream.range(0, DIM * DIM).forEach(i -> {
			Tile tile = getField(i).getTile();
			values.add(tile != null ? tile.getPoint() : null);
			vertical.add(tile != null ? tile.getColor(Location.OTHER) : null);
			left.add(tile != null ? tile.getColor(Location.LEFT) : null);
			right.add(tile != null ? tile.getColor(Location.RIGHT) : null);
		});
		return SpectrangleBoardPrinter.getBoardString(values, vertical, left, right);
	}

	// ------------------------- Commands ---------------------------

	/**
	 * Empties all fields of this <code>Board</code>.
	 */
	//@ ensures (\forall int i; 0 <= i & i < DIM * DIM; isEmptyField(i));
	public void reset() { // reset entire Board
		Arrays.stream(fields).filter(field -> !field.isEmpty()).forEach(field -> {
			field.setTile(null);
		});
	}

	/**
	 * Sets the content of field at index to the given <code>Tile</code>.
	 * @param index the field number
	 * @param tile the tile to be placed
	 */
	//@ ensures isField(index) && tile != null ==> getField(index).getTile() == tile;
	public void setField(int index, Tile tile) {
		if (isField(index) && tile != null) {
			Field field = getField(index);
			tile.setFacingUpwards(field.isFacingUpwards());
			field.setTile(tile);
		}
	}
	
	/**
	 * Sets the content of field at index corresponding to row and column
	 * to the given <code>Tile</code>.
	 * @param row row of field
	 * @param column column of field
	 * @param tile the tile to be placed
	 */
	/*@ ensures isField(index(row, column)) && tile != null ==>
				getField(index(row, column)).getTile() == tile;
	 */
	public void setField(int row, int column, Tile tile) {
		setField(index(row, column), tile);
	}
	
	/**
	 * Sets the content of <code>Field</code> according to the given <code>Move</code>.
	 * @param move move made
	 */
	//@ ensures move != null ==> getField(move.getIndex()).getTile() == move.getTile();
	public void setField(Move move) {
		if (move != null) {
			setField(move.getIndex(), move.getTile());
		}
	}

}
