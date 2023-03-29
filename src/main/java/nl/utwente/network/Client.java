package nl.utwente.network;

import nl.utwente.game.Board;
import nl.utwente.game.ComputerPlayer;
import nl.utwente.game.HumanPlayer;
import nl.utwente.game.NaiveStrategy;
import nl.utwente.game.Player;
import nl.utwente.game.Player.Move;
import nl.utwente.game.SmartComputerPlayer;
import nl.utwente.game.SmartStrategy;
import nl.utwente.game.Tile;
import nl.utwente.game.Tile.Location;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;
import java.util.stream.Collectors;

/**
 * Client for Spectrangle game.
 * @author Jordi Weldink & Yoon Hwan Jeong
 */
public class Client extends Thread {
	
	private static final String MODE_MANUAL = "manual";
	private static final String MODE_NAIVE = "naive";
	private static final String MODE_SMART = "smart";
	private static final String MODE_TOURNAMENT = "tournament";
	
	private int port;
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private String mode;
	private boolean isPlayingGame;
	private String inGameName;
	private Board board;
	private Player player;
	private List<Player> players;
	private List<Feature> features;

	/**
	 * Creates and runs <code>Client</code> and handles terminal input.
	 * @param args name of client and address and port of server
	 */
	@SuppressWarnings("resource")
	public static void main(String[] args) {
		Scanner scanner = new Scanner(System.in);
		String name = "";
		InetAddress inetAddress = null;
		int port = -1;
		while (name.isEmpty()) {
			System.out.print("Enter name: ");
			name = scanner.nextLine();
		}
		while (inetAddress == null) {
			System.out.print("Enter address: ");
			try {
				inetAddress = InetAddress.getByName(scanner.nextLine());
			} catch (UnknownHostException e) {
				System.out.println("Invalid address");
			}
		}
		boolean isPortValid = false;
		while (!isPortValid) {
			System.out.print("Enter port: ");
			try {
				port = Integer.parseInt(scanner.nextLine());
				isPortValid = port >= 0 && port <= 0xFFFF;
				if (!isPortValid) {
					System.out.println("Port must be between 0 and 65535");
				}
			} catch (NumberFormatException e) {
				System.out.println("Port must be integer");
			}
		}
		String mode = "";
		boolean isModeValid = false;
		while (mode.isEmpty() || !isModeValid) {
			System.out.print(String.format("Select mode [%s, %s, %s, %s]: ", MODE_MANUAL,
					MODE_NAIVE, MODE_SMART, MODE_TOURNAMENT));
			mode = scanner.nextLine();
			isModeValid = mode.equals(MODE_MANUAL) || mode.equals(MODE_NAIVE)
					|| mode.equals(MODE_SMART) || mode.equals(MODE_TOURNAMENT);
		}
		try {
			Client client = new Client(name, inetAddress, port, mode);
			client.start();
			client.handleTerminalInput();
		} catch (IOException e) {
			System.out.println("ERROR: failed constructing client");
		}
	}

	/**
	 * Constructs <code>Client</code>.
	 * @param name name of client
	 * @param host host to connect
	 * @param port port of host
	 * @param mode mode of client
	 * @throws IOException if an I/O error occurs when creating the socket
	 */
	public Client(String name, InetAddress host, int port, String mode) throws IOException {
		this(name, host, port, mode, new ArrayList<>());
	}

	/**
	 * Constructs <code>Client</code>.
	 * @param name name of client
	 * @param host host to connect
	 * @param port port of host
	 * @param mode mode of client
	 * @param features features to be enabled
	 * @throws IOException if an I/O error occurs when creating the socket
	 */
	public Client(String name, InetAddress host, int port, String mode, List<Feature> features) throws IOException {
		super(name);
		this.port = port;
		socket = new Socket(host, this.port);
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		this.mode = mode;
		this.features = features;
		this.features.stream().filter(feature -> feature.isClientSide() && !feature.isServerSide())
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
	}
	
	/**
	 * Reads <code>String</code> from terminal. 
	 * @param text text printed
	 * @return string read from terminal
	 */
	private String readString(String text) {
		System.out.print(text);
		String answer = null;
		try {
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(System.in));
			answer = bufferedReader.readLine();
		} catch (IOException e) {
			System.out.println("ERROR: problem occurred while reading string from terminal");
		}
		return answer == null ? "" : answer;
	}

	/**
	 * Acts according to command.
	 * @param command command from server
	 */
	private void onCommand(String command) {
		if (command.startsWith("server_features")) {
			System.out.println(command);
			List<String> enabledFeatures = features.stream()
					.filter(feature -> feature.isEnabled()).map(Feature::getName)
					.collect(Collectors.toList());
			sendMessage(
					"client_feature " + enabledFeatures.toString().replaceAll("[\\[\\]]", ""));
		} else if (command.startsWith("start")) {
			board = new Board();
			players = new ArrayList<>();
			String[] commands = command.split(" ");
			for (int i = 1; i < commands.length; i++) {
				if (commands[i].equals(inGameName)) {
					switch (mode) {
						case MODE_MANUAL:
							player = new HumanPlayer(inGameName);
							break;
						case MODE_NAIVE:
							player = new ComputerPlayer(inGameName, new NaiveStrategy());
							break;
						case MODE_SMART:
							player = new ComputerPlayer(inGameName, new SmartStrategy());
							break;
						case MODE_TOURNAMENT:
							player = new SmartComputerPlayer(inGameName);
							break;
					}
					players.add(player);
				} else {
					players.add(new HumanPlayer(commands[i]));
				}
				if (player instanceof SmartComputerPlayer) {
					((SmartComputerPlayer) player).setPlayers(players);
				}
			}
		} else if (command.startsWith("yourturn")) {
			System.out.println(board);
			String currentPlayerName = command.split(" ")[1];
			if (currentPlayerName.equals(inGameName)) {
				players.stream().filter(otherPlayer -> otherPlayer != player)
						.forEach(otherPlayer -> System.out.println(otherPlayer.getName()
								+ "'s tiles:\n" + otherPlayer.drawAllTiles()));
				System.out.println("Your tiles:\n" + player.drawAllTiles());
				if (player.hasPossibleMoves(board)) {
					Move move = player.determineMove(board);
					sendMessage("place " + move);
				} else {
					Tile tile = player.determineTileToExchange();
					if (tile != null) {
						sendMessage("discard " + tile);
					} else {
						sendMessage("pass");
					}
				}
			} else {
				System.out.println(currentPlayerName + "'s turn");
			}
		} else if (command.startsWith("place_update")) {
			String[] commands = command.split(" ");
			Tile tile = new Tile(commands[2]);
			int row = Integer.parseInt(commands[3]);
			int column = Integer.parseInt(commands[4]);
			Location orientation = Location.valueOf(commands[5].charAt(0));
			tile.setOrientation(orientation);
			Move move = new Move(row, column, tile);
			board.setField(move);
		} else if (command.startsWith("tiles_update")) {
			String[] commands = command.split(" ");
			String playerName = commands[1];
			Player updatedPlayer;
			if (player.getName().equals(playerName)) {
				updatedPlayer = player;
			} else {
				updatedPlayer = players.stream()
						.filter(otherPlayer -> otherPlayer.getName().equals(playerName)).findFirst()
						.orElse(null);
			}
			updatedPlayer.clearTiles();
			for (int i = 2; i < commands.length; i++) {
				updatedPlayer.addTile(new Tile(commands[i]));
			}
		} else if (command.startsWith("end")) {
			System.out.println(command);
			isPlayingGame = false;
			inGameName = "";
			board = null;
			player = null;
			players.clear();
		} else if (command.startsWith("error")) {
			if (Integer.parseInt(command.split(" ")[1]) == 1) {
				isPlayingGame = false;
			}
			System.err.println(command.substring(8));
		} else {
			System.out.println(command);
		}
	}

	/**
	 * Handles terminal input.
	 */
	public void handleTerminalInput() {
		while (true) {
			synchronized (this) {
				if (!isPlayingGame) {
					String input = readString("");
					Feature feature = features.stream().filter(f -> f.isEnabled() && input.startsWith(f.getCommandPrefix())).findFirst().orElse(null);
					if (feature != null) {
						feature.onCommand(input);
					} else {
						sendMessage(input);
					}
				}
			}
		}
	}

	/**
	 * Sends message to <code>ClientHandler</code>.
	 * @param message message to send
	 */
	public void sendMessage(String message) {
		try {
			if (message.matches("^play [2-4] [a-zA-Z]+$") && !isPlayingGame) {
				inGameName = message.split(" ")[2];
				isPlayingGame = true;
			}
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.out.println("ERROR: problem occurred while sending message");
			shutdown();
		}
	}

	/**
	 * Shutdowns <code>Client</code>.
	 */
	public void shutdown() {
		System.out.println("Shutdowning client");
		try {
			out.close();
			in.close();
			socket.close();
			System.exit(0);
		} catch (IOException e) {
			System.out.println("ERROR: problem occurred while shutdowning client");
		}
	}

	/**
	 * Reads message.
	 */
	@Override
	public void run() {
		String line;
		try {
			while ((line = in.readLine()) != null) {
				onCommand(line);
			}
		} catch (IOException e) {
			System.out.println("ERROR: problem occurred while reading message");
			shutdown();
		}
	}

}
