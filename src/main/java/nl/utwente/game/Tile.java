package nl.utwente.game;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Tile of Spectrangle game.
 * @author Yoon Hwan Jeong & Jordi Weldink
 *
 */
public class Tile implements Comparable<Tile> {
	
	/**
	 * Location of Tile.
	 * @author Yoon Hwan Jeong & Jordi Weldink
	 */
	public enum Location {

		RIGHT, OTHER, LEFT;

		/**
		 * Returns <code>Location</code> of given character. If <code>Location</code>
		 * cannot be found from given character, returns <code>null</code>.
		 * @param location character of location
		 * @return location of given character
		 */
		public static Location valueOf(char location) {
			switch (location) {
				case 'R':
					return RIGHT;
				case 'O':
					return OTHER;
				case 'L':
					return LEFT;
				default:
					return null;
			}
		}

		// ------------------------- Queries -------------------------

		/**
		 * Returns next <code>Location</code> (clockwise when <code>Tile</code> is
		 * facing upwards).
		 * @return next location
		 */
		// @ ensures \result.next().next() == this;
		/* @ pure @ */
		public Location next() {
			switch (this) {
				case RIGHT:
					return OTHER;
				case OTHER:
					return LEFT;
				default:
					return RIGHT;
			}
		}

		/**
		 * Returns opposite <code>Location</code>.
		 * @return opposite location
		 */
		// @ ensures \result.opposite() == this;
		/* @ pure @ */
		public Location opposite() {
			switch (this) {
				case RIGHT:
					return LEFT;
				case LEFT:
					return RIGHT;
				default:
					return OTHER;
			}
		}

		/**
		 * Returns flipped <code>Location</code>.
		 * @return flipped location
		 */
		// @ ensures \result.flip() == this;
		/* @ pure @ */
		public Location flip() {
			switch (this) {
				case RIGHT:
					return RIGHT;
				case OTHER:
					return LEFT;
				default:
					return OTHER;
			}
		}

		/* @ pure @ */
		@Override
		public String toString() {
			return Character.toString(name().charAt(0));
		}

	}

	// ------------------------- Constants -------------------------

	public static final char RED = 'R';
	public static final char YELLOW = 'Y';
	public static final char GREEN = 'G';
	public static final char BLUE = 'B';
	public static final char PURPLE = 'P';
	public static final char WHITE = 'W';
	public static final int MIN_POINT = 1;
	public static final int MAX_POINT = 6;
	
	// ------------------------- Instance variables -----------------
	
	private final String colors;
	private Map<Location, String> colorsByOrientation;
	private final int point;
	private Location orientation;
	private boolean facingUpwards;
	
	//@ private invariant colors != null && colors.length() == 3;
	//@ private invariant colorsByOrientation != null && colorsByOrientation.size() == 3;
	//@ private invariant point >= MIN_POINT && point <= MAX_POINT;
	//@ private invariant orientation != null;
	
	// ------------------------- Constructors -----------------------
	
	/**
	 * Constructs a <code>Tile</code> with orientation of <code>RIGHT</code>.
	 * @param colors colors of this tile
	 * @param point point of this tile
	 */
	//@ requires colors != null && colors.length == 3;
	//@ requires point >= MIN_POINT && point <= MAX_POINT;
	//@ ensures getOrientation() == Location.RIGHT;
	//@ ensures isFacingUpwards();
	public Tile(char[] colors, int point) {
		this.colors = String.valueOf(colors);
		colorsByOrientation = new HashMap<>();
		Arrays.stream(Location.values()).forEach(location -> {
			Location l = location.flip();
			colorsByOrientation.put(location, String.valueOf(new char[] {colors[l.ordinal()],
					colors[l.next().ordinal()], colors[l.next().next().ordinal()]}));
		});
		this.point = point;
		orientation = Location.RIGHT;
		facingUpwards = true;
	}
	
	/**
	 * Constructs <code>Tile</code> from <code>String</code>.
	 * @param tile string representation of tile
	 */
	//@ requires tile != null;
	public Tile(String tile) {
		this(tile.substring(0, 3).toCharArray(), Integer.parseInt(tile.substring(3)));
	}
	
	// ------------------------- Queries -------------------------
	
	/**
	 * Returns a color of this <code>Tile</code> at given location.
	 * @param location location of color
	 * @return color of this tile at given location
	 */
	/*@ ensures \result == RED || \result == YELLOW || \result == GREEN || \result == BLUE ||
	            \result == PURPLE || \result == WHITE;
	 */
	/*@ pure @*/
	public char getColor(Location location) {
		return colorsByOrientation.get(orientation).charAt(location.ordinal());
	}

	/**
	 * Returns colors of this <code>Tile</code>.
	 * @return colors of this tile
	 */
	/*@ pure @*/
	public String getColors() {
		return colors;
	}

	/**
	 * Returns point of this <code>Tile</code>.
	 * @return point of this tile
	 */
	/*@ pure @*/
	public int getPoint() {
		return point;
	}

	/**
	 * Returns orientation of this <code>Tile</code>.
	 * @return orientation of this tile
	 */
	/*@ pure @*/
	public Location getOrientation() {
		return orientation;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Tile</code> is facing upwards.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this tile is facing upwards, otherwise, false
	 */
	/*@ pure @*/
	public boolean isFacingUpwards() {
		return facingUpwards;
	}
	
	/**
	 * Returns <code>true</code> if this <code>Tile</code> is a joker.
	 * Otherwise, returns <code>false</code>.
	 * @return true if this tile is joker, otherwise, false
	 */
	/*@ pure @*/
	public boolean isJoker() {
		return colors.equals(String.valueOf(new char[] {WHITE, WHITE, WHITE}));
	}
	
	/**
	 * Returns <code>true</code> if this <code>Tile<code> matches color
	 * with given <code>Tile</code> at given <code>Location</code>. Otherwise,
	 * returns <code>false</code>.
	 * 
	 * @param location location of color
	 * @param tile     neighbour tile
	 * @return true if color matches, otherwise, false
	 */
	// @ requires tile != null;
	/* @ pure @ */
	public boolean matchColor(Location location, Tile tile) {
		return isJoker() || tile.isJoker()
				|| getColor(location) == tile.getColor(location.opposite());
	}
	
	/**
	 * Draws this <code>Tile</code>.
	 * @return drawing of this tile
	 */
	/*@ pure @*/
	public String draw() {
		String drawing = facingUpwards
				? String.format(
						"   / \\   \n" +
						"  / %d \\  \n" +
						" /%c   %c\\ \n" +
						"/   %c   \\\n" +
						"---------",
						point, getColor(Location.LEFT), getColor(Location.RIGHT),
						getColor(Location.OTHER))
				: String.format(
						"---------\n" +
						"\\   %c   /\n" +
						" \\%c   %c/ \n" +
						"  \\ %d /  \n" +
						"   \\ /   ",
						getColor(Location.OTHER), getColor(Location.LEFT), getColor(Location.RIGHT),
						point);
		return drawing;
	}
	
	/**
	 * Draws this <code>Tile</code> at given orientation.
	 * @param isFacingUpwards if true, drawing will be facing upwards
	 * @param paramOrientation orientation of this tile
	 * @return drawing of this tile at given orientation
	 */
	/*@ pure @*/
	public String draw(Location paramOrientation) {
		Tile tile = clone();
		tile.setOrientation(paramOrientation);
		return tile.draw();
	}

	/*@ pure @*/
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof Tile) {
			return colors.equals(((Tile) obj).colors) && point == ((Tile) obj).point;
		} else {
			return false;
		}
	}

	//@ also ensures \result != this && \result.equals(this);
	/*@ pure @*/
	@Override
	public Tile clone() {
		Tile tile = new Tile(colors.toCharArray(), point);
		tile.setOrientation(orientation);
		tile.setFacingUpwards(facingUpwards);
		return tile;
	}

	/*@ pure @*/
	@Override
	public String toString() {
		return colors + point;
	}
	
	/*@ pure @*/
	@Override
	public int compareTo(Tile o) {
		return Integer.compare(point, o.point);
	}
	
	// ------------------------- Commands -------------------------

	/**
	 * Orientates this <code>Tile</code> to given orientation.
	 * @param orientation orientation of this tile
	 */
	//@ requires orientation != null;
	//@ ensures getOrientation() == orientation;
	public void setOrientation(Location orientation) {
		this.orientation = orientation;
	}
	
	/**
	 * Sets whether this <code>Tile</code> is facing upwards or not.
	 * @param facingUpwards this tile faces upwards if true, otherwise, faces downwards
	 */
	//@ensures isFacingUpwards() == facingUpwards;
	public void setFacingUpwards(boolean facingUpwards) {
		if (this.facingUpwards != facingUpwards) {
			Map<Location, String> newColors = new HashMap<>();
			Arrays.stream(Location.values()).forEach(location -> {
				String string = colorsByOrientation.get(location);
				char rightColor = string.charAt(Location.RIGHT.ordinal());
				char otherColor = string.charAt(Location.OTHER.ordinal());
				char leftColor = string.charAt(Location.LEFT.ordinal());
				newColors.put(location.flip(),
						String.valueOf(new char[] {rightColor, leftColor, otherColor}));
			});
			colorsByOrientation = newColors;
		}
		this.facingUpwards = facingUpwards;
	}
	
	/**
	 * Resets this <code>Tile</code>.
	 * This method must be called before <code>Player</code> returns
	 * this <code>Tile</code> to <code>Bag</code>.
	 */
	//@ ensures isFacingUpwards() && getOrientation() == Location.RIGHT;
	public void reset() {
		setOrientation(Location.RIGHT);
		setFacingUpwards(true);
	}
	
}
