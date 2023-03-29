package nl.utwente.network;

import nl.utwente.game.Game;
import nl.utwente.game.Player;
import nl.utwente.game.Player.Move;
import nl.utwente.game.Tile;
import nl.utwente.network.ServerPlayer.State;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Game that can be played over network.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class ServerGame extends Game implements Runnable {

	private Server server;

	/**
	 * Constructs <code>ServerGame</code> at <code>Server</code> with given
	 * <code>ServerPlayer</code>s.
	 * @param server        server where server game is running at
	 * @param serverPlayers server players playing server game
	 */
	public ServerGame(Server server, ServerPlayer... serverPlayers) {
		this(server, Arrays.asList(serverPlayers));
	}

	/**
	 * Constructs <code>ServerGame</code> at <code>Server</code> with given
	 * <code>ServerPlayer</code>s.
	 * @param server        server where server game is running at
	 * @param serverPlayers server players playing server game
	 */
	public ServerGame(Server server, Collection<ServerPlayer> serverPlayers) {
		super(serverPlayers);
		this.server = server;
	}

	/**
	 * Returns <code>Server</code> of <code>ServerGame</code>.
	 * 
	 * @return server of server game
	 */
	public Server getServer() {
		return server;
	}

	/**
	 * Broadcasts to <code>ClientHandler</code>s playing in <code>ServerGame</code>.
	 * 
	 * @param message message to broadcast
	 */
	public void broadcast(String message) {
		server.broadcast(message, this);
	}

	/**
	 * Returns <code>ServerPlayer</code> corresponding to given
	 * <code>ClientHandler</code>.
	 * 
	 * @param clientHandler client handler that is playing in server game
	 * @return server player corresponding to given client handler
	 */
	public ServerPlayer getPlayer(ClientHandler clientHandler) {
		return players.stream().map(player -> (ServerPlayer) player)
				.filter(player -> player.getClientHandler() == clientHandler).findFirst()
				.orElse(null);
	}

	/**
	 * Returns <code>true</code> if given <code>ServerPlayer</code> is connected to
	 * <code>Server</code>.
	 * @param serverPlayer server player whose connection to server is to be tested
	 * @return true if given server player is connected to server
	 */
	public boolean isConnected(ServerPlayer serverPlayer) {
		return server.isConnected(serverPlayer.getClientHandler());
	}

	/**
	 * Returns <code>true</code> if it is given <code>ClientHandler</code>'s turn.
	 * 
	 * @param clientHandler client handler to check
	 * @return true if it is given client handler's turn
	 */
	public boolean isTurn(ClientHandler clientHandler) {
		return getPlayer(clientHandler) == currentPlayer;
	}

	/**
	 * Broadcasts <code>Player</code>s' <code>Tile</code>s in
	 * <code>ServerGame</code>.
	 */
	public void updateTiles() {
		players.stream().forEach(player -> {
			String tilesUpdate = "tiles_update " + player.getName() + " "
					+ player.getTiles().toString().replaceAll("[\\[,\\]]", "");
			broadcast(tilesUpdate);
		});
	}

	@Override
	public void run() {
		players.stream().forEach(player -> ((ServerPlayer) player).setServerGame(this));
		Collections.shuffle(players);
		broadcast("start " + players.stream().map(Player::getName).collect(Collectors.toList())
				.toString().replaceAll("[\\[,\\]]", ""));
		IntStream.range(0, Game.MAX_TILES).forEach(i -> {
			players.stream().forEach(player -> {
				player.addTile(bag.getRandomTile());
			});
		});
		updateTiles();
		gameLoop: while (!isOver()) {
			currentPlayer = getNextPlayer(currentPlayer);
			if (!isConnected((ServerPlayer) currentPlayer)) {
				broadcast("disconnected " + currentPlayer.getName());
				break;
			}
			broadcast("yourturn " + currentPlayer);
			if (currentPlayer.hasPossibleMoves(board)) {
				((ServerPlayer) currentPlayer).setState(State.PLACING);
				while (((ServerPlayer) currentPlayer).getState() == State.PLACING) {
					if (!isConnected((ServerPlayer) currentPlayer)) {
						broadcast("disconnected " + currentPlayer.getName());
						break gameLoop;
					}
					Move move = currentPlayer.determineMove(board);
					if (move != null) {
						board.setField(move);
						currentPlayer.removeTile(move.getTile());
						if (!bag.isEmpty()) {
							currentPlayer.addTile(bag.getRandomTile());
						}
						currentPlayer.addPoint(board.calculateScore(move.getIndex()));
						broadcast(String.format("place_update %s %s %d %d %s",
								currentPlayer.getName(), move.getTile(), move.getRow(),
								move.getColumn(), move.getTile().getOrientation()));
						break;
					}
				}
			} else {
				((ServerPlayer) currentPlayer).setState(
						!currentPlayer.getTiles().isEmpty() ? State.DISCARDING : State.PASSING);
				while (((ServerPlayer) currentPlayer).getState() == State.DISCARDING) {
					if (!isConnected((ServerPlayer) currentPlayer)) {
						broadcast("disconnected " + currentPlayer.getName());
						break gameLoop;
					}
					Tile tile = currentPlayer.determineTileToExchange();
					if (tile != null && !bag.isEmpty()) {
						currentPlayer.removeTile(tile);
						currentPlayer.addTile(bag.getRandomTile());
						bag.put(tile);
					}
				}
			}
			updateTiles();
		}
		StringBuilder endStringBuilder = new StringBuilder();
		endStringBuilder.append("end ");
		players.stream().forEach(player -> {
			endStringBuilder.append(player + " " + player.getPoint() + " ");
		});
		String end = endStringBuilder.toString();
		end = end.substring(0, end.lastIndexOf(" "));
		broadcast(end);
		server.onGameFinished(this);
	}

}
