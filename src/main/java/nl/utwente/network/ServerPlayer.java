package nl.utwente.network;

import nl.utwente.game.Board;
import nl.utwente.game.HumanPlayer;
import nl.utwente.game.Tile;
import nl.utwente.game.Tile.Location;

/**
 * Player that represents Client over network.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class ServerPlayer extends HumanPlayer {
	
	/**
	 * State of Player.
	 * @author Yoon Hwan Jeong & Jordi Weldink
	 */
	public enum State {
		
		WAITING, PLACING, DISCARDING, PASSING
		
	}
	
	private ServerGame serverGame;
	private ClientHandler clientHandler;
	private State state;
	private Move move;
	private Tile tile;

	/**
	 * Constructs <code>ServerPlayer</code> connected to given <code>ClientHandler</code>.
	 * @param clientHandler client handler connected to server player
	 */
	public ServerPlayer(ClientHandler clientHandler) {
		super(clientHandler.getName());
		serverGame = null;
		this.clientHandler = clientHandler;
		state = State.WAITING;
		move = null;
		tile = null;
	}
	
	/**
	 * Returns <code>ServerGame</code> that <code>ServerPlayer</code> is playing.
	 * @return server game that server player is playing
	 */
	public ServerGame getServerGame() {
		return serverGame;
	}

	/**
	 * Sets <code>ServerGame</code> that <code>ServerPlayer</code> is playing.
	 * Must be called when <code>ServerGame</code> starts.
	 * @param serverGame server game that server player is playing
	 */
	public void setServerGame(ServerGame serverGame) {
		this.serverGame = serverGame;
	}

	/**
	 * Returns <code>State</code> of <code>ServerPlayer</code>.
	 * @return state of server player
	 */
	public State getState() {
		return state;
	}

	/**
	 * Sets <code>State</code> of <code>ServerPlayer</code>.
	 * @param state state of server player
	 */
	public void setState(State state) {
		this.state = state;
	}

	/**
	 * Returns <code>ClientHandler</code> connected to <code>ServerPlayer</code>.
	 * @return
	 */
	public ClientHandler getClientHandler() {
		return clientHandler;
	}

	/**
	 * Parses place command and makes <code>Move</code>.
	 * @param command place command
	 */
	public void place(String command) {
		synchronized (this) {
			String[] commands = command.split(" ");
			Tile tileToPlace = getTile(commands[1]);
			if (tileToPlace != null) {
				int row = Integer.parseInt(commands[2]);
				int column = Integer.parseInt(commands[3]);
				Location orientation = Location.valueOf(commands[4].charAt(0));
				tileToPlace.setOrientation(orientation);
				move = new Move(row, column, tileToPlace);
			}
		}
	}
	
	/**
	 * Parses discard or pass command and choose <code>Tile</code> to discard or pass turn.
	 * @param command discard or pass command
	 */
	public void discardOrPass(String command) {
		synchronized (this) {
			if (command.startsWith("discard")) {
				String[] commands = command.split(" ");
				tile = getTile(commands[1]);
				if (tile == null) {
					clientHandler.sendMessage("error 2 invalid move");
				}
			} else {
				state = State.PASSING;
			}
		}
	}
	
	@Override
	public Move determineMove(Board board) {
		synchronized (this) {
			if (move != null) {
				if (board.isValidMove(move)) {
					Move determinedMove = move.clone();
					move = null;
					state = State.WAITING;
					return determinedMove;
				} else {
					clientHandler.sendMessage("error 2 invalid move");
					move = null;
					return null;
				}
			} else {
				return null;
			}
		}
	}

	@Override
	public Tile determineTileToExchange() {
		synchronized (this) {
			if (state == State.DISCARDING) {
				if (tile != null) {
					Tile determinedTile = tile.clone();
					tile = null;
					state = State.WAITING;
					return determinedTile;
				} else {
					return null;
				}
			} else {
				state = State.WAITING;
				return null;
			}
		}
	}

}
