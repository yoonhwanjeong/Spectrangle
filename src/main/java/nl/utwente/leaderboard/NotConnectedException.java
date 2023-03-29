package nl.utwente.leaderboard;

import java.sql.SQLException;

/**
 * Exception thrown when Query is not connected to database.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
@SuppressWarnings("serial")
public class NotConnectedException extends SQLException {

	public NotConnectedException() {
		super("Query is not connected to database");
	}
	
}
