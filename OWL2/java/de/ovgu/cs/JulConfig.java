/**
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License") 1.1!
 * You may not use this file except in compliance with the License.
 *
 * See  https://spdx.org/licenses/CDDL-1.1.html  for the specific
 * language governing permissions and limitations under the License.
 *
 * Copyright (c) 2022 Jens Elkner (jel+hets@cs.ovgu.de).
 */

import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.util.logging.LogManager;

/**
 * A java.util.logging (JUL) configuration class.
 *
 * This JUL configurator is intentend to be used for hets and its java sub
 * systems. However, it is generic and thus re-usable e.g. via
 * {@code java -Djava.util.logging.config.class=LogConfig ...}.
 *
 * If the environment variable {@code HETS_JUL_CFG} is set to a JUL config file,
 * this will be read and used for JUL configuration. If this environment variable
 * is not set, the java system property {@code java.util.logging.config.file}
 * will be used instead. If this one is unset, too or loading the related JUL
 * config file fails, an in-memory-configuration gets loaded instead. In this
 * case if the environment variable {@code HETS_LOG_LEVEL} is set to
 * {@code SEVERE, WARNING, INFO or CONFIG, FINE, FINER, FINEST} or {@code 1 .. 5}
 * respectively, the default log level gets set accordingly. Otherwise the
 * default level {@code SEVERE} will be used.
 *
 * @author Jens Elkner
 */
public class JulConfig {
	static final void loadConfig() {
		String s;
		try {
			s = System.getenv("HETS_JUL_CFG");
		} catch (Exception e) {
			s = null;
		}
		if (s == null) {
			try {
				s = System.getenv("java.util.logging.config.file");
			} catch (Exception e) {
				s = null;
			}
		}
		if (s != null) {
			FileInputStream fis = null;
			try {
				fis = new FileInputStream(s);
				LogManager.getLogManager().readConfiguration(fis);
				return;
			} catch (Exception e) {
				System.err.println("Unable to load HETS_JUL_CFG: "
					+ e.getLocalizedMessage());
			} finally {
				if (fis != null) {
					try { fis.close(); } catch (Exception x) { /* ignore */ }
				}
			}
		}
		// Per default we do not want to log any warnings or infos because hets
		// would assume because of this, that there was an error.
		String lvl = "SEVERE";
		int l = 0;
		// However, if invoked directly, one should have the opportunity to
		// enable logging of less severe messages without having to specify
		// a full log config, by just setting the env var HETS_LOG_LEVEL.
		try {
			s = System.getenv("HETS_LOG_LEVEL");
		} catch (Exception e) {
			s = null;
		}
		if (s != null) {
			s = s.toUpperCase().trim();
			if (s.equals("0") || s.equals("SEVERE") || s.equals("FATAL")
				|| s.equals("ERROR"))
			{
				lvl = "SEVERE";
				l = 0;
			} else if ( s.equals("1") || s.equals("WARNING")
				|| s.equals("WARN"))
			{
				lvl = "WARNING";
				l = 1;
			} else if ( s.equals("2") || s.equals("INFO")
				|| s.equals("CONFIG"))
			{
				lvl = "CONFIG";
				l = 2;
			} else if ( s.equals("3") || s.equals("FINE")) {
				lvl = "FINE";
				l = 3;
			} else if ( s.equals("4") || s.equals("FINER")) {
				lvl = "FINER";
				l = 4;
			} else if ( s.equals("5") || s.equals("FINEST")
				|| s.equals("DEBUG"))
			{
				lvl = "FINEST";
				l = 5;
			}
			// else: use default
		}
		
		// for better readability we used a in-memory-config instead of setting
		// it up programmatically. See default logging.properties of the jvm.
		s = System.lineSeparator();
		String cfg =
"handlers= java.util.logging.ConsoleHandler" + s +
".level= " + lvl + s +
"java.util.logging.FileHandler.pattern = %h/java%u.log" + s +
"java.util.logging.FileHandler.limit = 50000" + s +
"java.util.logging.FileHandler.count = 1" + s +
"java.util.logging.FileHandler.maxLocks = 100" + s +
"java.util.logging.FileHandler.formatter = java.util.logging.XMLFormatter" + s +
"java.util.logging.ConsoleHandler.level = " + lvl + s +
"java.util.logging.SimpleFormatter.format= " +
	"%1$tF %1$tT.%1$tL %4$s [%2$s] - %5$s" + (l > 2 ? "%6$s%n" : "%n") + s +
"java.util.logging.ConsoleHandler.formatter = java.util.logging.SimpleFormatter"
			;
		ByteArrayInputStream bis = null;
		try {
			bis = new ByteArrayInputStream(cfg.getBytes("UTF-8"));
			LogManager.getLogManager().readConfiguration(bis);
		} catch (Exception e) {
			System.err.println("Failed to configre logging system: "
				+ e.getLocalizedMessage());
		} finally {
				if (bis != null) {
					try { bis.close(); } catch (Exception x) { /* ignore */ }
				}
		}
	}

	public JulConfig() {
		loadConfig();
	}
}
