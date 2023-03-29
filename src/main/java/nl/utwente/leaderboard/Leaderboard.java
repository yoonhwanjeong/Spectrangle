package nl.utwente.leaderboard;

import nl.utwente.game.Player;
import nl.utwente.network.CannotDisableFeatureException;
import nl.utwente.network.CannotEnableFeatureException;
import nl.utwente.network.Feature;

import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Timestamp;

/**
 * Server-side Leaderboard Feature.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public class Leaderboard implements Feature {

	private boolean isEnabled;
	private Query query;

	/**
	 * Updates score.
	 * @param player player whose score will be updated
	 * @param time time when <code>Game</code> is finished
	 */
	public void update(Player player, long time) {
		try {
			PreparedStatement preparedStatement = query
					.prepareStatement("insert into score values (?, ?, ?, ?)");
			preparedStatement.setString(1, player.getUUID().toString());
			preparedStatement.setString(2, player.getName());
			preparedStatement.setInt(3, player.getPoint());
			preparedStatement.setTimestamp(4, new Timestamp(time));
			preparedStatement.executeUpdate();
		} catch (SQLException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Gets given number of top scores.
	 * @param numberOfScores number of scores to get
	 * @return given number of top scores
	 */
	public String getTopScores(int numberOfScores) {
		StringBuilder stringBuilder = new StringBuilder();
		try {
			ResultSet resultSet = query.executeQuery(
					"select * from score order by Point desc limit " + numberOfScores);
			while (resultSet.next()) {
				String player = resultSet.getString("Player");
				int point = resultSet.getInt("Point");
				Timestamp timestamp = resultSet.getTimestamp("Time");
				stringBuilder.append(String.format("Player: %s, Point: %d, Time: %s\n", player,
						point, timestamp));
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		String string = stringBuilder.toString();
		string = string.substring(0, string.lastIndexOf("\n"));
		return string;
	}

	/**
	 * Gets scores above given point.
	 * @param minimumPoint lower boundary of point
	 * @return scores above given point
	 */
	public String getScoresAbove(int minimumPoint) {
		StringBuilder stringBuilder = new StringBuilder();
		try {
			ResultSet resultSet = query.executeQuery(
					"select * from score where Point >= " + minimumPoint + " order by Point desc");
			while (resultSet.next()) {
				String player = resultSet.getString("Player");
				int point = resultSet.getInt("Point");
				Timestamp timestamp = resultSet.getTimestamp("Time");
				stringBuilder.append(String.format("Player: %s, Point: %d, Time: %s\n", player,
						point, timestamp));
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		String string = stringBuilder.toString();
		string = string.substring(0, string.lastIndexOf("\n"));
		return string;
	}

	/**
	 * Gets scores below given point.
	 * @param maximumPoint upper boundary of point
	 * @return scores below given point
	 */
	public String getScoresBelow(int maximumPoint) {
		StringBuilder stringBuilder = new StringBuilder();
		try {
			ResultSet resultSet = query.executeQuery(
					"select * from score where Point <= " + maximumPoint + " order by Point desc");
			while (resultSet.next()) {
				String player = resultSet.getString("Player");
				int point = resultSet.getInt("Point");
				Timestamp timestamp = resultSet.getTimestamp("Time");
				stringBuilder.append(String.format("Player: %s, Point: %d, Time: %s\n", player,
						point, timestamp));
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		String string = stringBuilder.toString();
		string = string.substring(0, string.lastIndexOf("\n"));
		return string;
	}

	/**
	 * Gets average of points.
	 * @return average of points
	 */
	public String getScoresAverage() {
		StringBuilder stringBuilder = new StringBuilder();
		try {
			ResultSet resultSet = query
					.executeQuery("select avg(Point) as AveragePoint from score");
			while (resultSet.next()) {
				double point = resultSet.getDouble("AveragePoint");
				stringBuilder.append("Average score: " + point);
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		return stringBuilder.toString();
	}

	/**
	 * Gets average of points on given day.
	 * @param day day in "YYYY-MM-DD" format
	 * @return average of points on given day
	 */
	public String getScoresAverage(String day) {
		StringBuilder stringBuilder = new StringBuilder();
		try {
			String minimumDay = day + " 00:00:00";
			String maximumDay = day + " 23:59:59";
			ResultSet resultSet = query
					.executeQuery("select avg(Point) as AveragePoint from score where Time >= '"
							+ minimumDay + "' and Time <= '" + maximumDay + "'");
			while (resultSet.next()) {
				double point = resultSet.getDouble("AveragePoint");
				stringBuilder.append("Average score on " + day + ": " + point);
			}
		} catch (SQLException e) {
			e.printStackTrace();
		}
		return stringBuilder.toString();
	}

	@Override
	public String getName() {
		return "Leaderboard";
	}

	@Override
	public String getCommandPrefix() {
		return "leaderboard";
	}

	@Override
	public String getCommands() {
		return "leaderboard top <numberOfScores>: View top <numberOfScores> scores\n" +
				"leaderboard above <point>: View scores above <point> points\n" +
				"leaderboard below <point>: View scores below <point> points\n" +
				"leaderboard average: View average of all scores\n" +
				"leaderboard average <YYYY-MM-DD>: View average of scores on <YYYY-MM-DD>";
	}

	@Override
	public String onCommand(String command) {
		if (command.matches("^leaderboard help$")) {
			return getCommands();
		} else if (command.matches("^leaderboard top [1-9]\\d*$")) {
			return getTopScores(Integer.parseInt(command.split(" ")[2]));
		} else if (command.matches("^leaderboard above [1-9]\\d*$")) {
			return getScoresAbove(Integer.parseInt(command.split(" ")[2]));
		} else if (command.matches("^leaderboard below [1-9]\\d*$")) {
			return getScoresBelow(Integer.parseInt(command.split(" ")[2]));
		} else if (command.matches("^leaderboard average$")) {
			return getScoresAverage();
		} else if (command.matches("^leaderboard average "
				+ "([12][0-9]{3}-(0[1-9]|1[0-2])-(0[1-9]|[12][0-9]|3[01]))$")) {
			return getScoresAverage(command.split(" ")[2]);
		} else {
			return "error 6 invalid parameters";
		}
	}

	@Override
	public boolean isEnabled() {
		return isEnabled;
	}

	@Override
	public boolean isClientSide() {
		return false;
	}

	@Override
	public boolean isServerSide() {
		return true;
	}

	@Override
	public void enable() throws CannotEnableFeatureException {
		query = Query.getInstance("localhost", 3306, "root", "root", "spectrangle_leaderboard",
				"useSSL=false");
		try {
			query.connect();
			isEnabled = true;
		} catch (ClassNotFoundException | SQLException e) {
			throw new CannotEnableFeatureException(this);
		}
	}

	@Override
	public void disable() throws CannotDisableFeatureException {
		if (!isEnabled && query.isConnected()) {
			try {
				query.disconnect();
				isEnabled = false;
			} catch (SQLException e) {
				throw new CannotDisableFeatureException(this);
			}
		}
	}

}
