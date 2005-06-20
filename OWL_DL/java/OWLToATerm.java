/*
 * Created on Mar 9, 2005
 *
 */

/**
 * @author jiang
 */

import org.semanticweb.owl.model.OWLOntology;
// import org.semanticweb.owl.io.Renderer;
import org.semanticweb.owl.io.Parser;
import org.mindswap.pellet.utils.*;

// import gnu.getopt.LongOpt;
// import gnu.getopt.Getopt;
// import org.semanticweb.owl.util.OWLConnection;
import org.semanticweb.owl.util.OWLManager;
// import org.semanticweb.owl.model.OWLException;
// import org.semanticweb.owl.impl.model.*;
// import org.semanticweb.owl.model.*;
// import org.semanticweb.owl.io.simple.*;
import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
import org.semanticweb.owl.io.owl_rdf.OWLRDFParser;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.net.URI;
import java.util.Map;
// import java.util.HashMap;
// import java.util.Iterator;
// import org.apache.log4j.BasicConfigurator;
import org.semanticweb.owl.validation.OWLValidationConstants;
import uk.ac.man.cs.img.owl.validation.SpeciesValidator;
// import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
// import uk.ac.man.cs.img.owl.validation.ConstructChecker;
// import org.xml.sax.SAXException;
import org.semanticweb.owl.util.URIMapper;
import org.xml.sax.SAXException;
// import org.semanticweb.owl.util.PropertyBasedURIMapper;
// import java.util.Properties;
// import java.net.URISyntaxException;
// import java.io.FileInputStream;
// import java.io.IOException;
import aterm.pure.*;
import aterm.*;
import java.util.*;
import java.io.*;

// import javax.swing.filechooser.FileFilter;
// import org.mindswap.pellet.owlapi.*;
// import org.mindswap.pellet.*;

public class OWLToATerm implements OWLValidationConstants {

	static public void main(String[] args) {

		if (args.length != 1) { System.out.println("Usage: processor <URI>");
		  System.exit(1); }
		 
		OWLRDFParser rdfParser = null;
		Parser parser = null;
		OWLOntology onto = null;

		// LongOpt[] longopts = new LongOpt[11];
		boolean warnings = false;
		// boolean constructs = false;
		boolean noImports = false;
		String uriMapping = "";
		int validation = -1;
		ATermFactory factory = new PureFactory();

		// BasicConfigurator.configure();


		try {

			URI uri = new URI(args[0]);
			// URI uri = new URI("file:///D:/JOB/wine.xml");
			URIMapper mapper = null;

			/* Use the RDF Parser */
			rdfParser = new OWLRDFParser();

			
		
			// Warning
			List warningList;
			OWLToATermErrorHandler handler = new OWLToATermErrorHandler();

			rdfParser.setOWLRDFErrorHandler(handler);

			warningList = handler.getList();

			parser = rdfParser;
			
			parser.setConnection(OWLManager.getOWLConnection());
			if (mapper != null) {
				Map opt = new HashMap();
				opt.put("uriMapper", mapper);
				parser.setOptions(opt);
			}

			onto = parser.parseOntology(uri);
			
			// Validation
			SpeciesValidator sv = new SpeciesValidator();
			Map options = new HashMap();
			options.put("uriMapper", mapper);
			if (noImports) {
				options.put("ignoreSchemaImports", new Boolean(true));
			}
			sv.setOptions(options);

			if (sv.isOWLLite(onto)) {
				validation = LITE;
			} else if (sv.isOWLDL(onto)) {
				validation = DL;
			} else if (sv.isOWLFull(onto)) {
				validation = FULL;
			}
			
		    owlParserOutput(validation, warningList, onto);
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}

	
	static void owlParserOutput(int valid, List message, OWLOntology ontology) {

		try {
			File file = new File("./output2.term");
			if(file.exists()){
				file.delete();
				file.createNewFile();
			}
			// FileWriter fw = new FileWriter(file, true);
			PrintWriter pw = new PrintWriter(new FileWriter(file, true));
			
			Renderer2 renderer = new Renderer2();
			ATerm result;
			Writer writer = new StringWriter();
			
			String validation = new String();
			switch (valid){
				case LITE:
					 validation = "This is OWL " + "Lite.";
					 break;
			    case DL: 
					 validation = "This is OWL " + "DL.";
					 break;
			    case FULL: 
					 validation = "This is OWL " + "Full.";
					 break;
			    // default: validation = "gemischet!\n";
					 
			}
			
			// pw.println(validation);
			// for(Iterator it = message.iterator(); it.hasNext(); ){
			// 	pw.println((String) it.next() + ".");
			//}
			// pw.println();
			pw.close();
			
			FileOutputStream stream = new FileOutputStream( file, true );
			renderer.renderOntology( ontology, writer );
			result = ATermUtils.term( writer.toString() );
			result.writeToSharedTextFile( stream );		    
			// System.out.println(result);
		    // pw.close();
		    stream.close();

		} catch (Exception e) {
			System.out.println(e);		
		}
	}

}


class OWLToATermErrorHandler implements OWLRDFErrorHandler {

	ArrayList list;

	public OWLToATermErrorHandler() {
		list = new ArrayList();
	}

	public void owlFullConstruct(int code, String message) throws SAXException {
	}

	public void owlFullConstruct(int code, String message, Object obj)
			throws SAXException {
	}

	public void error(String message) throws SAXException {
		list.add(message);
		// throw new SAXException();
	}

	public void warning(String message) throws SAXException {
		list.add(message);
	}

	public List getList() {
		return list;
	}

}

