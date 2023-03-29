package nl.utwente.network;

/**
 * Exception thrown when Feature cannot be enabled.
 * @author Yoon Hwan Jeong & Jordi Weldink
 */
@SuppressWarnings("serial")
public class CannotEnableFeatureException extends Exception {

	public CannotEnableFeatureException(Feature feature) {
		super("could not enable " + feature.getName());
	}

}
