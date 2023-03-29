package nl.utwente.game;

/**
 * ComputerPlayer that uses Strategy.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class ComputerPlayer extends Player {
	
	// ------------------------- Instance variables -----------------
	
	private Strategy strategy;
	
	//@ private invariant strategy != null;
	
	// ------------------------- Constructors -----------------------

	/**
	 * Constructs <code>ComputerPlayer</code> with given <code>Strategy</code>.
	 * @param strategy strategy of computer player
	 */
	//@ requires strategy != null;
	public ComputerPlayer(Strategy strategy) {
		super(strategy.getName() + "Computer");
		this.strategy = strategy;
	}
	
	/**
	 * Constructs <code>ComputerPlayer</code> with given name and <code>Strategy</code>.
	 * @param name name of computer player
	 * @param strategy strategy of computer player
	 */
	//@ requires name != null && strategy != null;
	public ComputerPlayer(String name, Strategy strategy) {
		super(name);
		this.strategy = strategy;
	}
	
	// ------------------------- Queries ----------------------------
	
	/**
	 * Returns <code>Strategy</code> of <code>ComputerPlayer</code>.
	 * @return strategy of computer player
	 */
	public Strategy getStrategy() {
		return strategy;
	}

	@Override
	public Move determineMove(Board board) {
		return strategy.determineMove(board, getTiles());
	}

	@Override
	public Tile determineTileToExchange() {
		return strategy.determineTileToExchange(getTiles());
	}
	
}
