package nl.utwente.game;

import nl.utwente.game.Tile.Location;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

/**
 * HumanPlayer that uses console to play.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class HumanPlayer extends Player {
	
	// ------------------------- Constructors -----------------------

	/**
	 * Constructs a <code>HumanPlayer</code> with given name.
	 * @param name name of this human player
	 */
	//@ requires name != null && name.matches("[a-zA-Z]+");
	public HumanPlayer(String name) {
		super(name);
	}
	
	// ------------------------- Queries ----------------------------
	
	/**
	 * Reads an <code>Integer</code> from standard input.
	 * @param prompt message to be displayed
	 * @return integer read
	 */
	//@ requires prompt != null;
	private int readInt(String prompt) {
		int value = 0;
		boolean intRead = false;
		@SuppressWarnings("resource")
		Scanner line = new Scanner(System.in);
		do {
			System.out.print(prompt);
			try (Scanner scannerLine = new Scanner(line.nextLine());) {
				if (scannerLine.hasNextInt()) {
					intRead = true;
					value = scannerLine.nextInt();
				}
			}
		} while (!intRead);
		return value;
	}
	
	/**
	 * Asks this <code>HumanPlayer</code> which <code>Field</code> to play.
	 * @param board current game board
	 * @return index of field to play
	 */
	//@ requires board != null;
	//@ ensures board.isPlayableField(\result);
	private int chooseField(Board board) {
		List<Integer> fields = new ArrayList<>();
		for (int i = 0; i < Board.DIM * Board.DIM; i++) {
			if (board.isPlayableField(i)) {
				label: for (Tile tile : getTiles()) {
					for (Location orientation : Location.values()) {
						Tile clone = tile.clone();
						clone.setOrientation(orientation);
						if (board.isValidMove(i, clone)) {
							fields.add(i);
							break label;
						}
					}
				}
			}
		}
		String prompt = "Choose which field to play " + fields + ": ";
		int choice = readInt(prompt);
		boolean valid = fields.contains(choice);
		while (!valid) {
			System.out.println("ERROR: field " + choice + " is not valid choice.");
			choice = readInt(prompt);
			valid = fields.contains(choice);
		}
		return choice;
	}
	
	/**
	 * Asks this <code>HumanPlayer</code> which <code>Tile</code> to discard.
	 * @return tile to discard
	 */
	//@ requires !getTiles().isEmpty();
	//@ ensures hasTile(\result);
	private Tile chooseTile() {
		String prompt = "Choose 0 to pass your turn or\n" +
				"Choose which tile to discard [1.." + getTiles().size() + "]: ";
		int choice = readInt(prompt);
		boolean valid = choice >= 0 && choice <= getTiles().size();
		while (!valid) {
			System.out.println("ERROR: tile " + choice + " is not valid choice.");
			choice = readInt(prompt);
			valid = choice >= 0 && choice <= getTiles().size();
		}
		return choice == 0 ? null : getTiles().get(choice - 1);
	}
	
	/**
	 * Asks this <code>HumanPlayer</code> which <code>Tile</code> to play.
	 * @param board current game board
	 * @param index index of field to play
	 * @return tile to play
	 */
	//@ requires board != null && board.isPlayableField(index);
	//@ ensures hasTile(\result);
	private Tile chooseTile(Board board, int index) {
		String prompt = "Choose which tile to play [1.." + getTiles().size() + "]: ";
		int choice = readInt(prompt);
		boolean valid = false;
		label: while (!valid) {
			if (choice - 1 >= 0 && choice - 1 < getTiles().size()) {
				for (Location orientation : Location.values()) {
					Tile tile = getTiles().get(choice - 1).clone();
					tile.setOrientation(orientation);
					if (board.isValidMove(index, tile)) {
						valid = true;
						break label;
					}
				}
			}
			System.out.println("ERROR: tile " + choice + " is not valid choice.");
			choice = readInt(prompt);
		}
		return getTiles().get(choice - 1);
	}
	
	/**
	 * Asks this <code>HumanPlayer</code> which orientation to play.
	 * @param board current game board
	 * @param index index of field to play
	 * @param tile tile to play
	 * @return orientation to play
	 */
	//@ requires board != null && board.isPlayableField(index) && tile != null && hasTile(tile);
	private Location chooseOrientation(Board board, int index, Tile tile) {
		Tile clone = tile.clone();
		clone.setFacingUpwards(board.getField(index).isFacingUpwards());
		System.out.println(drawAllOrientations(clone));
		String prompt = "Choose which permutation to play [1.." + Location.values().length + "]: ";
		int choice = readInt(prompt);
		boolean valid = false;
		label: while (!valid) {
			if (choice - 1 >= 0 && choice - 1 < Location.values().length) {
				clone = tile.clone();
				clone.setOrientation(Location.values()[choice - 1]);
				if (board.isValidMove(index, clone)) {
					valid = true;
					break label;
				}
			}
			System.out.println("ERROR: permutation " + choice + " is not valid choice.");
			choice = readInt(prompt);
		}
		return Location.values()[choice - 1];
	}

	@Override
	public Move determineMove(Board board) {
		int index = chooseField(board);
		Tile tile = chooseTile(board, index);
		Location orientation = chooseOrientation(board, index, tile);
		Field field = board.getField(index);
		tile.setOrientation(orientation);
		return new Move(field.getRow(), field.getColumn(), tile);
	}

	@Override
	public Tile determineTileToExchange() {
		return chooseTile();
	}

}
