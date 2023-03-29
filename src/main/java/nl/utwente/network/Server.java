package nl.utwente.network;

import nl.utwente.leaderboard.Leaderboard;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Scanner;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Server that can host Spectrangle games.
 * @author Jordi Weldink & Yoon Hwan Jeong
 */
public class Server {

	private int port;
	private ServerSocket serverSocket;
	private List<Feature> features;
	private List<ClientHandler> clientHandlers;
	private Map<ClientHandler, Integer> waitingClientHandlers;
	private Map<ServerGame, Set<ClientHandler>> playingClientHandlers;

	/**
	 * Creates and runs <code>Server</code> and listens for <code>Client</code>.
	 */
	public static void main(String[] args) {
		Scanner scanner = new Scanner(System.in);
		int port = -1;
		boolean isPortValid = false;
		while (!isPortValid) {
			try {
				System.out.print("Enter port: ");
				port = Integer.parseInt(scanner.nextLine());
				isPortValid = port >= 0 && port <= 0xFFFF;
				if (!isPortValid) {
					System.out.println("Port must be between 0 and 65535");
				} else {
					try {
						List<Feature> features = new ArrayList<>();
						System.out.println("Enable leaderboard feature (y/n)? ");
						if (scanner.nextLine().equalsIgnoreCase("y")) {
							features.add(new Leaderboard());
						}
						Server server = new Server(port, features);
						scanner.close();
						server.run();
					} catch (IOException e) {
						System.out.println("Port is already in use");
						isPortValid = false;
					}
				}
			} catch (NumberFormatException e) {
				System.out.println("Port must be integer");
			}
		}
	}

	/**
	 * Constructs <code>Server</code>.
	 * @param port port that server listens to
	 * @throws IOException if port is already in use
	 */
	public Server(int port) throws IOException {
		this(port, new ArrayList<>());
	}

	/**
	 * Constructs <code>Server</code>.
	 * @param port port that server listens to
	 * @param features list of features to be enabled
	 * @throws IOException if port is already in use
	 */
	public Server(int port, List<Feature> features) throws IOException {
		long currentTime = System.currentTimeMillis();
		this.port = port;
		serverSocket = new ServerSocket(this.port);
		this.features = features;
		this.features.stream().filter(feature -> !feature.isClientSide() && feature.isServerSide())
				.forEach(feature -> {
					try {
						feature.enable();
					} catch (CannotEnableFeatureException e) {
						System.err.println(e.getMessage());
					}
				});
		List<String> enabledFeatures = this.features.stream().filter(feature -> feature.isEnabled())
				.map(Feature::getName).collect(Collectors.toList());
		System.out.println(
				"Enabled features: " + enabledFeatures.toString().replaceAll("[\\[\\]]", ""));
		clientHandlers = new ArrayList<>();
		waitingClientHandlers = new HashMap<>();
		playingClientHandlers = new HashMap<>();
		System.out.println(
				"Server loaded in " + (System.currentTimeMillis() - currentTime) + " ms");
	}

	/**
	 * Returns <code>Feature</code> of given name.
	 * @param featureName name of feature
	 * @return feature of given name
	 */
	public Feature getFeature(String featureName) {
		return features.stream().filter(feature -> feature.getName().equals(featureName))
				.findFirst().orElse(null);
	}

	/**
	 * Returns <code>List</code> of <code>Feature</code>s that <code>Server</code> has.
	 * @return list of features that server has
	 */
	public List<Feature> getFeatures() {
		return features;
	}

	/**
	 * Returns <code>List</code> of enabled <code>Feature</code>s that <code>Server</code> has.
	 * @return list of enabled features that server has
	 */
	public List<Feature> getEnabledFeatures() {
		return features.stream().filter(feature -> feature.isEnabled())
				.collect(Collectors.toList());
	}

	/**
	 * Returns <code>true</code> if <code>Feature</code> of given name is enabled.
	 * @param featureName name of feature
	 * @return true if feature of given name is enabled
	 */
	public boolean isFeatureEnabled(String featureName) {
		Feature feature = getFeature(featureName);
		return feature != null && feature.isEnabled();
	}

	/**
	 * Listens for <code>Client</code> and creates <code>ClientHandler</code>.
	 */
	public void run() {
		while (true) {
			try {
				Socket socket = serverSocket.accept();
				ClientHandler clientHandler = new ClientHandler(this, socket);
				clientHandler.start();
				List<String> enabledFeatures = features.stream()
						.filter(feature -> feature.isEnabled()).map(Feature::getName)
						.collect(Collectors.toList());
				clientHandler.sendMessage(
						"server_feature " + enabledFeatures.toString().replaceAll("[\\[\\]]", ""));
				addHandler(clientHandler);
			} catch (IOException e) {
				System.out.println("ERROR: problem occurred while listening for client");
			}
		}
	}

	/**
	 * Adds <code>ClientHandler</code>.
	 * @param clientHandler client handler to add
	 */
	public void addHandler(ClientHandler clientHandler) {
		synchronized (this) {
			clientHandlers.add(clientHandler);
			System.out.println(clientHandler.getInetAddress() + " connected");
		}
	}

	/**
	 * Removes <code>ClientHandler</code>.
	 * @param clientHandler client handler to remove
	 */
	public void removeHandler(ClientHandler clientHandler) {
		synchronized (this) {
			playingClientHandlers.entrySet().stream()
					.filter(entry -> entry.getValue().contains(clientHandler))
					.forEach(entry -> entry.getValue().remove(clientHandler));
			if (waitingClientHandlers.containsKey(clientHandler)) {
				int numberOfPlayers = waitingClientHandlers.get(clientHandler);
				waitingClientHandlers.remove(clientHandler);
				Set<ClientHandler> clientHandlerSet = waitingClientHandlers.entrySet().stream()
						.filter(entry -> entry.getValue() == numberOfPlayers).map(Entry::getKey)
						.collect(Collectors.toSet());
				clientHandlerSet.stream().forEach(
						handler -> handler.sendMessage("waiting " + clientHandlerSet.size()));
			}
			clientHandlers.remove(clientHandler);
			System.out.println(clientHandler.getInetAddress() + " disconnted");
		}
	}

	/**
	 * Sends message to all <code>ClientHandler</code>s.
	 * @param message message to broadcast
	 */
	public void broadcast(String message) {
		synchronized (this) {
			for (ClientHandler clientHandler : clientHandlers) {
				clientHandler.sendMessage(message);
			}
		}
	}

	/**
	 * Sends message to all <code>ClientHandler</code>s in <code>ServerGame</code>.
	 * @param message message to broadcast
	 * @param serverGame played game
	 */
	public void broadcast(String message, ServerGame serverGame) {
		synchronized (this) {
			for (ClientHandler clientHandler : playingClientHandlers.get(serverGame)) {
				clientHandler.sendMessage(message);
			}
		}
	}

	/**
	 * Returns <code>true</code> if <code>ClientHandler</code> is connected to <code>Server</code>.
	 * @param clientHandler client handler to check connection
	 * @return true if client handler is connected to server
	 */
	public boolean isConnected(ClientHandler clientHandler) {
		synchronized (this) {
			return clientHandler == null || clientHandlers.contains(clientHandler);
		}
	}

	/**
	 * Returns <code>true</code> if <code>ClientHandler</code> is playing game.
	 * @param clientHandler client handler to check
	 * @return true if client handler is playing game
	 */
	public boolean isPlayingGame(ClientHandler clientHandler) {
		synchronized (this) {
			return playingClientHandlers.entrySet().stream()
					.filter(entry -> entry.getValue().contains(clientHandler)).findFirst()
					.orElse(null) != null;
		}
	}

	/**
	 * Adds <code>ClientHandler</code> to waiting list. If there are enough players
	 * to start game, moves <code>ClientHandler</code>s to playing list and starts
	 * game.
	 * @param clientHandler client handler to add
	 * @param numberOfPlayers number of players required to start game
	 * @param name name of client handler
	 */
	public void play(ClientHandler clientHandler, int numberOfPlayers, String name) {
		synchronized (this) {
			boolean isNameTaken = clientHandlers.stream()
					.filter(handler -> handler != clientHandler && name.equals(handler.getName()))
					.findFirst().orElse(null) != null;
			if (!isNameTaken) {
				clientHandler.setName(name);
				Set<ClientHandler> clientHandlerSet = waitingClientHandlers.entrySet().stream()
						.filter(entry -> entry.getValue() == numberOfPlayers).map(Entry::getKey)
						.collect(Collectors.toSet());
				clientHandlerSet.forEach(handler -> handler.sendMessage("entered " + name));
				clientHandlerSet.add(clientHandler);
				if (clientHandlerSet.size() == numberOfPlayers) {
					ServerGame serverGame = new ServerGame(this, clientHandlerSet.stream()
							.map(ServerPlayer::new).collect(Collectors.toSet()));
					new Thread(serverGame).start();
					playingClientHandlers.put(serverGame, clientHandlerSet);
					clientHandlerSet.stream()
							.forEach(handler -> waitingClientHandlers.remove(handler));
				} else {
					clientHandlerSet.forEach(
							handler -> handler.sendMessage("waiting " + clientHandlerSet.size()));
					waitingClientHandlers.put(clientHandler, numberOfPlayers);
				}
			} else {
				clientHandler.sendMessage("error 1 username is taken");
			}
		}
	}

	/**
	 * Returns <code>ServerGame</code> that <code>ClientHandler</code> is playing.
	 * @param clientHandler client handler that is playing game
	 * @return server game that client handler is playing
	 */
	public ServerGame getServerGame(ClientHandler clientHandler) {
		synchronized (this) {
			return playingClientHandlers.entrySet().stream()
					.filter(entry -> entry.getValue().contains(clientHandler)).map(Entry::getKey)
					.findFirst().orElse(null);
		}
	}

	/**
	 * Acts when <code>ServerGame</code> is finished.
	 * @param serverGame server game that is just finished
	 */
	public void onGameFinished(ServerGame serverGame) {
		if (isFeatureEnabled("Leaderboard")) {
			Leaderboard leaderboard = (Leaderboard) getFeature("Leaderboard");
			long currentTime = System.currentTimeMillis();
			serverGame.getPlayers().stream().forEach(plaer -> {
				leaderboard.update(plaer, currentTime);
			});
		}
		playingClientHandlers.remove(serverGame);
	}

	/**
	 * Prints message to <code>Server</code> console.
	 * @param message message to print
	 */
	public void print(String message) {
		System.out.println(message);
	}

}
