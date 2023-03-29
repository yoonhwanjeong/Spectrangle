package nl.utwente.leaderboard;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

/**
 * Query connected to database.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class Query {
	
	private static Query query;

    private Connection connection;
    private Statement statement;
    private ResultSet resultSet;
    private String host;
    private int port;
    private String username;
    private String password;
    private String database;
    private String options;
    private boolean connected;

    /**
     * Returns instance of <code>Query</code>.
     * @param host host of database
     * @param port port of database
     * @param username username of database
     * @param password password of database
     * @param database database to connect
     * @return instance of query
     */
    public static Query getInstance(String host, int port, String username, String password,
			String database) {
		return getInstance(host, port, username, password, database, "");
	}

    /**
     * Returns instance of <code>Query</code>.
     * @param host host of database
     * @param port port of database
     * @param username username of database
     * @param password password of database
     * @param database database to connect
     * @param options options of connection
     * @return instance of query
     */
	public static Query getInstance(String host, int port, String username, String password,
			String database, String options) {
		if (query == null) {
			query = new Query(host, port, username, password, database, options);
			return query;
		}
		return query;
	}

	/**
	 * Constructs <code>Query</code>.
	 * @param host host of database
     * @param port port of database
     * @param username username of database
     * @param password password of database
     * @param database database to connect
     * @param options options of connection
     * @return instance of query
	 */
	private Query(String host, int port, String username, String password, String database,
			String options) {
		this.port = port;
		this.host = "jdbc:mysql://" + host + ":" + this.port + "/";
		this.username = username;
		this.password = password;
		this.database = database;
		this.options = options;
	}

	/**
	 * Returns <code>true</code> if <code>Query</code> is connected to database.
	 * @return true if query is connected to database
	 */
	public boolean isConnected() {
	    return connected;
	}

	/**
	 * Connects <code>Query</code> to database.
	 * @throws ClassNotFoundException if mysql-connector-java is not found
	 * @throws SQLException           if a database access error occurs or this
	 *                                method is called on a closed connection
	 */
	public void connect() throws ClassNotFoundException, SQLException {
		Class.forName("com.mysql.cj.jdbc.Driver");
		connection = DriverManager.getConnection(host + database + "?" + options, username,
				password);
		statement = connection.createStatement();
		connected = true;
	}

	/**
	 * Disconnects <code>Query</code> from database.
	 * @throws SQLException if a database access error occurs
	 */
    public void disconnect() throws SQLException {
        if (resultSet != null && !resultSet.isClosed()) {
            resultSet.close();
            resultSet = null;
        }
        if (statement != null && !statement.isClosed()) {
            statement.close();
            statement = null;
        }
        if (connection != null && !connection.isClosed()) {
            connection.close();
            connection = null;
        }
        connected = false;
        query = null;
    }
    
	/**
	 * Creates a <code>PreparedStatement</code> object for sending parameterized SQL
	 * statements to the database.
	 * @param sql an SQL statement that may contain one or more '?' IN parameter
	 *            placeholders
	 * @return a new default <code>PreparedStatement</code> object containing the
	 *         pre-compiled SQL statement
	 * @throws SQLException if a database access error occurs or this method is
	 *                      called on a closed connection
	 */
    public PreparedStatement prepareStatement(String sql) throws SQLException {
    	if (!connected) {
    		throw new NotConnectedException();
    	}
		return connection.prepareStatement(sql);
    }

	/**
	 * Executes the given SQL statement, which may return multiple results.
	 * @param sql any SQL statement
	 * @return <code>true</code> if the first result is a <code>ResultSet</code>
	 *         object; <code>false</code> if it is an update count or there are no
	 *         results
	 * @throws SQLException if a database access error occurs, this method is called
	 *                      on a closed <code>Statement</code>, the method is called
	 *                      on a <code>PreparedStatement</code> or
	 *                      <code>CallableStatement</code>
	 */
    public boolean execute(String sql) throws SQLException {
    	if (!connected) {
    		throw new NotConnectedException();
    	}
        return statement.execute(sql);
    }

	/**
	 * Executes the given SQL statement, which returns a single
	 * <code>ResultSet</code> object.
	 * @param sql an SQL statement to be sent to the database, typically a static
	 *            SQL <code>SELECT</code> statement
	 * @return a <code>ResultSet</code> object that contains the data produced by
	 *         the given query; never <code>null</code>
	 * @throws SQLException if a database access error occurs, this method is called
	 *                      on a closed <code>Statement</code>, the given SQL
	 *                      statement produces anything other than a single
	 *                      <code>ResultSet</code> object, the method is called on a
	 *                      <code>PreparedStatement</code> or
	 *                      <code>CallableStatement</code>
	 */
    public ResultSet executeQuery(String sql) throws SQLException {
    	if (!connected) {
	        throw new NotConnectedException();
    	}
        return statement.executeQuery(sql);
    }

	/**
	 * Executes the given SQL statement, which may be an <code>INSERT</code>,
	 * <code>UPDATE</code>, or <code>DELETE</code> statement or an SQL statement
	 * that returns nothing, such as an SQL DDL statement.
	 * @param sql an SQL Data Manipulation Language (DML) statement, such as
	 *            <code>INSERT</code>, <code>UPDATE</code> or <code>DELETE</code>;
	 *            or an SQL statement that returns nothing, such as a DDL statement.
	 * @return either (1) the row count for SQL Data Manipulation Language (DML)
	 *         statements or (2) 0 for SQL statements that return nothing
	 * @throws SQLException if a database access error occurs, this method is called
	 *                      on a closed <code>Statement</code>, the given SQL
	 *                      statement produces a <code>ResultSet</code> object, the
	 *                      method is called on a <code>PreparedStatement</code> or
	 *                      <code>CallableStatement</code>
	 */
    public int executeUpdate(String sql) throws SQLException {
    	if (!connected) {
    		throw new NotConnectedException();
    	}
	    return statement.executeUpdate(sql);
    }
	
}
