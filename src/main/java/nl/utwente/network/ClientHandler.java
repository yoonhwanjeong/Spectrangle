package nl.utwente.network;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.text.SimpleDateFormat;
import java.util.Date;

/**
 * ClientHandler that handles communication between Client and Server.
 * @author Jordi Weldink & Yoon Hwan Jeong
 */
public class ClientHandler extends Thread {

	private Server server;
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;

	/**
	 * Constructs <code>ClientHandler</code>.
	 * @param server server to connect
	 * @param socket socket to communicate
	 */
	public ClientHandler(Server server, Socket socket) throws IOException {
		this.server = server;
		this.socket = socket;
		in = new BufferedReader(new InputStreamReader(this.socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(this.socket.getOutputStream()));
	}

	/**
	 * Shutdowns <code>ClientHandler</code>.
	 */
	private void shutdown() {
		server.removeHandler(this);
	}
	
	/**
	 * Acts according to command.
	 * @param command command from client
	 */
	private void onCommand(String command) {
		int error = -1;
		if (command.startsWith("client_features")) {
			return;
		} else if (command.startsWith("play")) {
			if (!server.isPlayingGame(this)) {
				if (command.matches("^play [2-4] [a-zA-Z]+$")) {
					String[] commands = command.split(" ");
					server.play(this, Integer.parseInt(commands[1]), commands[2]);
				} else {
					error = 6;
				}
			} else {
				error = 5;
			}
		} else if (command.startsWith("place")) {
			if (server.isPlayingGame(this)) {
				if (server.getServerGame(this).isTurn(this)) {
					if (command.matches("^place [RYGBPW]{3}[1-6] [0-5] -?[0-5] [ROL]$")) {
						if (server.getServerGame(this).getPlayer(this)
								.hasPossibleMoves(server.getServerGame(this).getBoard())) {
							server.getServerGame(this).getPlayer(this).place(command);
						} else {
							error = 5;
						}
					} else {
						error = 6;
					}
				} else {
					error = 3;
				}
			} else {
				error = 5;
			}
		} else if (command.startsWith("discard") || command.matches("^pass$")) {
			if (server.isPlayingGame(this)) {
				if (server.getServerGame(this).isTurn(this)) {
					if (command.matches("^discard [RYGBPW]{3}[1-6]$")
							|| command.matches("^pass$")) {
						if (!server.getServerGame(this).getPlayer(this)
								.hasPossibleMoves(server.getServerGame(this).getBoard())) {
							server.getServerGame(this).getPlayer(this).discardOrPass(command);
						} else {
							error = 5;
						}
					} else {
						error = 6;
					}
				} else {
					error = 3;
				}
			} else {
				error = 5;
			}
		} else {
			Feature feature = server.getEnabledFeatures().stream()
					.filter(f -> command.startsWith(f.getCommandPrefix())).findFirst().orElse(null);
			if (feature != null) {
				sendMessage(feature.onCommand(command));
			} else {
				error = 4;
			}
		}
		if (error > -1) {
			String description;
			switch (error) {
				case 0:
					description = "unidentified";
					break;
				case 1:
					description = "username is taken";
					break;
				case 2:
					description = "invalid move";
					break;
				case 3:
					description = "not your turn";
					break;
				case 4:
					description = "unknown command";
					break;
				case 5:
					description = "invalid command";
					break;
				case 6:
					description = "invalid parameters";
					break;
				default:
					description = "error that should not occur";
					break;
			}
			sendMessage("error " + error + " " + description);
		}
	}

	/**
	 * Returns <code>InetAddress</code> of <code>ClientHandler</code>.
	 * @return address of client handler
	 */
	public InetAddress getInetAddress() {
		return socket.getInetAddress();
	}

	/**
	 * Sends message to <code>Client</code>.
	 * @param message message to send
	 */
	public void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * Reads message from <code>Client</code>.
	 */
	@Override
	public void run() {
		String line;
		try {
			while ((line = in.readLine()) != null) {
				String timestamp = new SimpleDateFormat("HH:mm:ss").format(new Date());
				server.print("<" + timestamp + "> " + this + ": " + line);
				onCommand(line);
			}
		} catch (IOException e) {
			shutdown();
		}
	}

}
