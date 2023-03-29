package nl.utwente.network;

/**
 * Exception thrown when Feature cannot be disabled.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
@SuppressWarnings("serial")
public class CannotDisableFeatureException extends Exception {

	public CannotDisableFeatureException(Feature feature) {
		super("could not disable " + feature.getName());
	}

}
