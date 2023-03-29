package nl.utwente;

import nl.utwente.network.Client;
import nl.utwente.network.Server;

/**
 * Main class of jar file.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class Main {
	
	private static final String USAGE = "java -jar Spectrangle.jar <server|client>";

	/**
	 * Main method that is called when program is ran from jar file.
	 * @param args server or client
	 */
	public static void main(String[] args) {
		if (args.length != 1) {
			System.out.println(USAGE);
			System.exit(0);
		}
		if (args[0].equals("server")) {
			Server.main(new String[] {});
		} else if (args[0].equals("client")) {
			Client.main(new String[] {});
		} else {
			System.out.println(USAGE);
			System.exit(0);
		}
	}

}
