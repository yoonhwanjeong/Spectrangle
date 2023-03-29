package nl.utwente.network;

/**
 * Feature of Client and/or Server.
 * 
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
public interface Feature {

	/**
	 * Returns name of <code>Feature</code>.
	 * @return name of feature
	 */
	String getName();
	
	/**
	 * Returns command prefix of <code>Feature</code>.
	 * @return command prefix of feature
	 */
	String getCommandPrefix();
	
	/**
	 * Returns commands of <code>Feature</code>.
	 * @return commands of feature
	 */
	String getCommands();
	
	/**
	 * Acts according to command.
	 * @param command command of feature
	 * @return response if command is valid, otherwise, error
	 */
	String onCommand(String command);

	/**
	 * Returns <code>true</code> if <code>Feature</code> is enabled.
	 * @return true if feature is enabled
	 */
	boolean isEnabled();

	/**
	 * Returns <code>true</code> if <code>Feature</code> is client-side.
	 * @return true if feature is client-side
	 */
	boolean isClientSide();

	/**
	 * Returns <code>true</code> if <code>Feature</code> is server-side.
	 * @return true if feature is server-side
	 */
	boolean isServerSide();

	/**
	 * Enables <code>Feature</code>.
	 * @throws CannotEnableFeatureException if there was problem while
	 *         enabling <code>Feature</code>.
	 */
	void enable() throws CannotEnableFeatureException;

	/**
	 * Disables <code>Feature</code>.
	 * @throws CannotDisableFeatureException if there was problem while
	 *         disabling <code>Feature</code>.
	 */
	void disable() throws CannotDisableFeatureException;

}
