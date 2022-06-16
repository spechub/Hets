import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.net.HttpURLConnection;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URL;
import java.net.URLConnection;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.zip.GZIPInputStream;
import java.util.zip.GZIPOutputStream;

import org.semanticweb.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.semanticweb.owlapi.rdf.rdfxml.renderer.RDFXMLRenderer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLOntologyDocumentSource;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.StreamDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportEvent;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.MissingImportListener;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.util.OWLOntologyMerger;

import uk.ac.manchester.cs.owl.owlapi.OWLOntologyIRIMapperImpl;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;

public class OWL2Parser {

	private static enum OPTION {
		OWL_XML, MANCHESTER, RDF_XML, OBO, TURTLE
	}

	private static Boolean quick = false;
	private static Boolean cyclic = false;
	protected static final Set<IRI> missingImports = new HashSet<IRI>();
	private static Set<OWLOntology> ontologies;
	private static final Set<OWLOntology> exported = new HashSet<OWLOntology>();
	private static OWLOntologyManager manager =
		setupManagerWithMissingImportListener();
	private static OWLOntologyIRIMapperImpl mapper =
		new OWLOntologyIRIMapperImpl();
	private static URI uri = null;
	private static int maxRedirects = 0;

	private static void checkMaxRedirects() {
		String t = System.getProperty("http.maxRedirects", null);
		if (t == null || t.isEmpty()) {
			maxRedirects = 20;
			return;
		}
		try {
			int n = Integer.parseInt(t, 10);
			if (n > 0) {
				maxRedirects = n;
			}
		} catch (NumberFormatException nfe) {
			System.err.println("Ignoring invalid system property "
				+ "'http.maxRedirects' - invalid number '" + t + "'");
		}
	}

	private static URLConnection getConnection(URL url, int redirCount)
		throws IOException
	{
		URLConnection c = url.openConnection();
		if (!(c instanceof HttpURLConnection)) {
			return c;
		}
		HttpURLConnection con = (HttpURLConnection) c;
		con.addRequestProperty("Accept", "text/plain");
		con.setConnectTimeout(300 * 1000);	// 5 min timeout
		int status = con.getResponseCode();
		if (status == HttpURLConnection.HTTP_MOVED_TEMP
			|| status == HttpURLConnection.HTTP_MOVED_PERM
			|| status == HttpURLConnection.HTTP_SEE_OTHER)
		{
			if (redirCount > maxRedirects) {
				System.err.println("Max. redirects (" + maxRedirects
					+ ") reached for " + url);
				return null;
			}
			String loc = null;
			try {
				loc = con.getHeaderField("Location");
				if (loc == null) {
					System.err.println("Invalid redirect by '" + url
						+ "' (missing Location header).");
					return null;
				}
				url = new URL(loc);
			} catch (MalformedURLException mue) {
				System.err.println("'" + url + "' redirects to an unsupported "
					+ "resource (" + loc + ")");
				return null;
			}
			con.disconnect();
			return getConnection(url, redirCount + 1);
		} else if (status != HttpURLConnection.HTTP_OK) {
			System.err.println("URL '" + url + "' is not OK (status " + status
				+ ").");
			return null;
		}
		return con;
	}

	public static void main(String[] args) {
		boolean failed = false;
		// A simple example of how to load and save an ontology
		try {
			OWLOutputHandler out = new OWLOutputHandler();
			parseArgs(args, out);
			checkMaxRedirects();
			URLConnection con = getConnection(uri.toURL(), 0);
			if (con == null) {
				System.err.println("Nothing to parse - exiting.");
				System.exit(1);
			}
			StreamDocumentSource sds =
				new StreamDocumentSource(con.getInputStream(), IRI.create(uri));
			OWLOntologyLoaderConfiguration config =
				new OWLOntologyLoaderConfiguration();
			config = config
				.setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
			config = config.setFollowRedirects(true);
			OWLOntology ontology =
				manager.loadOntologyFromOntologyDocument(sds, config);
			if ( !missingImports.isEmpty()) {
				IRI ontohub = IRI.create("https://ontohub.org/external/");
				for (IRI mi : missingImports) {
					mapper.addMapping(mi, ontohub.resolve(mi.toURI().getHost()
						+ mi.toURI().getPath()));
				}
				// reset the manager. clear out imports to avoid duplicates
				manager = setupManagerWithMissingImportListener();
				manager.addIRIMapper(mapper);
				// collect missing imports again to report them in output file.
				missingImports.clear();
				ontology =
					manager.loadOntologyFromOntologyDocument(sds, config);
			}
			ontologies = getImports(ontology, new HashSet<OWLOntology>());
			out._open();
			if (cyclic) {
				String str = ontology.getOntologyID().getOntologyIRI().toString();
				// we must make a new name
				String merged_name = str + ".merged.owl";
				// System.out.println("NAME: " + merged_name + "\n");
				IRI mergedOntologyIRI = IRI.create(merged_name);
				// System.out.println("MERGED_IRI " + mergedOntologyIRI + "\n");
				OWLOntology merged;
				// Axioms can be excluded when 'quick' Option selected
				if (quick) {
					merged = manager.createOntology(mergedOntologyIRI);
				} else {
					OWLOntologyMerger merger = new OWLOntologyMerger(manager);
					merged =
						merger.createMergedOntology(manager, mergedOntologyIRI);
				}
				out.renderUsingOption(merged);
			} else {
				ontologies.add(ontology);
				exportImports(out);
			}
			out._close();
		} catch (Exception ex) {
			System.err.println("OWL parse error: " + ex.getMessage());
			failed = true;
		}
		System.exit(failed ? 1 : 0);
	}

	// print usage information screen
	private static void showHelpScreen() {
		System.out.println("Usage: processor [<options..>] <URI>\n"
			+ "_>_options_<______________\n"
			+ " | -o <tp> <fn>  ..write output to file\n"
			+ " - - - tp  <- type [: owl xml omn rdf obo dol ttl]\n"
			+ " - - - fn  <- filename\n"
			+ " | -o-sys <tp> ..write output to system.out\n"
			+ " - - - - - tp  <- type\n"
			+ " | -qk  ..internal(!) sets 'quick' option\n"
			+ " | -h  ..this helptext");
	}

	// parse arguments according to option set
	// fails for unknown or incomplete arguments, or when IRI is not set
	private static void parseArgs(String[] args, OWLOutputHandler out)
		throws Exception
	{
		String inp = "", msg = "OWL2Parser.parseArgs: ";
		if (args.length == 0) {
			throw new Exception(msg + "no arguments provided");
		}
		for (int i = 0; i < args.length; i++ ) {
			String arg = args[i].toLowerCase();
			if (arg.startsWith("-")) {
				if (arg.equals("-o")) {
					if (!(i < args.length - 2)) {
						throw new Exception(msg
							+ "insufficient arguments (-o [format] [filename])");
					}
					out.add(parseOption(args[++i].toLowerCase(), msg), args[++i]);
				} else if (arg.equals("-o-sys")) {
					if (!(i < args.length - 1)) {
						throw new Exception(msg
							+ "insufficient arguments (-o-sys [format])");
					}
					out.add(parseOption(args[ ++i].toLowerCase(), msg));
				} else if (arg.equals("-qk") || arg.equals("-q")) {
					quick = true;
				} else if (arg.equals("-h") || arg.equals("--help")) {
					showHelpScreen();
				} else {
					throw new Exception(msg + "unknown command <" + arg + ">");
				}
			} else {
				if (!inp.equals("")) {
					throw new Exception(msg + "ambigious IRI");
				}
				inp = args[i]; // read again to undo earlier 'toLowerCase'
				if (arg.startsWith("http:") || arg.startsWith("https:")) {
					uri = new URI(inp);
				} else {
					uri = new File(inp).toURI();
				}
			}
		}
		if (inp.equals("")) {
			throw new Exception(msg + "IRI not set");
		}
	}

	private static OPTION parseOption(String opt, String err) throws Exception {
		if (opt.equals("xml") || opt.equals("owl")) {
			return OPTION.OWL_XML;
		} else if (opt.equals("omn")) {
			return OPTION.MANCHESTER;
		} else if (opt.equals("rdf")) {
			return OPTION.RDF_XML;
		} else if (opt.equals("obo")) {
			return OPTION.OBO;
		} else if (opt.equals("ttl")) {
			return OPTION.TURTLE;
		}
		throw new Exception(err + "unrecognized owl-format: " + opt);
	}

	private static OWLOntologyManager setupManagerWithMissingImportListener() {
		OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
		mgr.addMissingImportListener(new HasMissingImports());
		return mgr;
	}

	private static class HasMissingImports implements MissingImportListener {
		@Override
		public void importMissing(MissingImportEvent event) {
			missingImports.add(event.getImportedOntologyURI());
		}
	}

	private static Set<OWLOntology> getImports(OWLOntology ontology,
		Set<OWLOntology> stop)
	{
		Set<OWLOntology> s = new HashSet<OWLOntology>();
		Set<OWLOntology> next = new HashSet<OWLOntology>(stop);
		next.add(ontology);
		for (OWLOntology imported : ontology.getDirectImports()) {
			if (cyclic || next.contains(imported)) {
				cyclic = true;
			} else if (!s.contains(imported)) {
				Set<OWLOntology> i = getImports(imported, next);
				s.add(imported);
				s.addAll(i);
			}
		}
		return s;
	}

	private static void exportImports(OWLOutputHandler out) throws IOException {
		Boolean changed;
		do {
			changed = false;
			for (OWLOntology onto : ontologies) {
				if (exported.containsAll(onto.getDirectImports())) {
					if (!exported.contains(onto)) {
						changed = exported.add(onto);
						out.renderUsingOption(onto);
					}
				}
			}
		} while (changed);
	}

	// output handler allows and handles a list of output-requests
	protected static class OWLOutputHandler {
		static ArrayList<OWLOntologyWriter> writer =
			new ArrayList<OWLOntologyWriter>();

		void add(OPTION op) throws Exception {
			writer.add(new OWLOntologyWriter(op));
		}

		void add(OPTION op, String filename) throws Exception {
			writer.add(new OWLOntologyWriter(filename, op));
		}

		void _open() throws IOException {
			for (OWLOntologyWriter out : writer) {
				out._open();
			}
		}

		void _close() throws IOException {
			for (OWLOntologyWriter out : writer) {
				out._close();
			}
		}

		// function need to be called once to render and close every output
		void renderUsingOption(OWLOntology onto) throws IOException {
			for (OWLOntologyWriter out : writer) {
				out.renderUsingOption(onto);
			}
		}
	}

	// custem OntolgyWriter bundles a BufferedWriter with an OWL output format
	protected static class OWLOntologyWriter extends BufferedWriter {
		protected static OPTION option;

		OWLOntologyWriter(String fn, OPTION op) throws Exception {
			super(new FileWriter(fn));
			option = op;
		}

		OWLOntologyWriter(OPTION op) throws Exception {
			super(new OutputStreamWriter(System.out));
			option = op;
		}

		void writeMissingImports() throws IOException {
			for (IRI mi : missingImports) {
				write("<Missing>" + mi + "</Missing>\n");
			}
		}

		void _open() throws IOException {
			if (option == OPTION.OWL_XML) {
				write("<Ontologies>\n");
			}
		}

		void _close() throws IOException {
			if (option == OPTION.OWL_XML) {
				writeMissingImports();
				write("\n</Ontologies>\n");
			}
			_close(this);
		}

		void _close(Writer pointer) throws IOException {
			pointer.flush();
			pointer.close();
		}

		void renderUsingOption(OWLOntology onto) throws IOException {
			switch (option) {
				case OWL_XML:
					renderAsXml(onto);
					break;
				case MANCHESTER:
					renderAsOmn(onto);
					break;
				case RDF_XML:
					renderAsRdf(onto);
					break;
				// TODO: the below still need implementation!
				case OBO:
					renderAsXml(onto);
					break;
				case TURTLE:
					renderAsXml(onto);
					break;
			}
		}

		void renderAsOmn(OWLOntology onto) {
			try {
				ManchesterOWLSyntaxRenderer omnrend =
					new ManchesterOWLSyntaxRenderer();
				omnrend.render(onto, new PrintWriter(this));
			} catch (OWLRendererException ex) {
				System.err.println("Error by ManchesterParser!");
				ex.printStackTrace();
			}
		}

		void renderAsXml(OWLOntology onto) {
			FileOutputStream fos = null;
			FileInputStream fis = null;
			OutputStreamWriter out = null;
			InputStreamReader in = null;
			char[] buf = new char[8192];
			int c, n;
			int chomp = -1;
			try {
				OWLXMLRenderer xmlren = new OWLXMLRenderer();
				String t = System.getenv("HETS_GZIP");
				boolean gz = t == null || t.equalsIgnoreCase("on");
				t = gz ? ".xml.gz" : ".xml";
				String tmpDir = System.getenv("TMPDIR");
				File tempFile = File.createTempFile("owlTemp_1", t,
					tmpDir == null ? null : new File(tmpDir));
				fos = new FileOutputStream(tempFile);
				out = new OutputStreamWriter(gz
					? new GZIPOutputStream(fos, 4096)
					: fos,
					"UTF-8");
				if (quick) {
					onto.getOWLOntologyManager()
						.removeAxioms(onto,onto.getAxioms());
				}
				xmlren.render(onto, new PrintWriter(out));
				out.close();
				out = null;
				fos = null;
				fis = new FileInputStream(tempFile);
				in = new InputStreamReader(gz
					? new GZIPInputStream(fis, 4096)
					: fis,
					"UTF-8");
				// ignore the first line containing <?xml version="1.0"?>
				while ((chomp != -2) && (c = in.read(buf, 0, 8192)) != -1) {
					if (chomp == -1) {
						n = 0;
						while (n < c && buf[n] != '\n' && buf[n] != '\r') {
							n++;
						}
						if (n < c) {
							chomp = n;
						}
					}
					if (chomp != -1) {
						// chomp trailing LF and CR
						n = chomp;
						chomp = 0;
						while (n < c && (buf[n] == '\n' || buf[n] == '\r')) {
							n++;
						}
						if (n < c) {
							write(buf, n, c - n);
							chomp = -2;
						}
					}
				}
				// copy the remaining stuff as is
				while ((c = in.read(buf, 0, 8192)) != -1) {
					write(buf, 0, c);
				}
				in.close();
				in = null;
				fis = null;
				t = System.getenv("HETS_KEEPTMP");
				if (t == null || ! t.equalsIgnoreCase("on")) {
					tempFile.deleteOnExit();
				}
				append("<Loaded name=\"")
					.append(manager.getOntologyDocumentIRI(onto))
					.append("\" ontiri=\"")
					.append(onto.getOntologyID().getOntologyIRI().get())
					.append("\"/>\n");
			} catch (Exception ex) {
				System.err.println("Error by XMLParser!");
				ex.printStackTrace();
			} finally {
				if (out != null) {
					try { out.close(); } catch (Exception e) { /* nwcd */ }
				} else if (fos != null) {
					try { fos.close(); } catch (Exception e) { /* nwcd */ }
				}
				if (in != null) {
					try { in.close(); } catch (Exception e) { /* nwcd */ }
				} else if (fis != null) {
					try { fis.close(); } catch (Exception e) { /* nwcd */ }
				}
			}
		}

		void renderAsRdf(OWLOntology onto) {
      try {
        RDFXMLRenderer rdfrend = new RDFXMLRenderer(onto, new PrintWriter(this));
        rdfrend.render();
      } catch (IOException ex) {
				System.err.println("Error by RDFParser!");
				ex.printStackTrace();
			}
		}
	}
}
