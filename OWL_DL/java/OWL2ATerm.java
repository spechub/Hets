/*
 * Created on Mar 15, 2005
 *
 */

/**
 * @author jiang
 *
 */

import org.semanticweb.owl.model.OWLOntology;
// import org.semanticweb.owl.io.Renderer;
import org.semanticweb.owl.io.Parser;
// import org.mindswap.pellet.utils.*;
// import gnu.getopt.LongOpt;
// import gnu.getopt.Getopt;
// import org.semanticweb.owl.util.OWLConnection;
import org.semanticweb.owl.util.OWLManager;
// import org.semanticweb.owl.model.OWLException;
// import org.semanticweb.owl.impl.model.*;
import org.semanticweb.owl.model.*;   // Class Axiom
// import org.semanticweb.owl.io.simple.*;
import org.semanticweb.owl.io.owl_rdf.OWLRDFParser;
// import java.io.StringWriter;
// import java.io.Writer;
import java.util.HashMap;
import java.net.URI;
import java.util.Map;
// import java.util.HashMap;
// import java.util.Iterator;
// import org.apache.log4j.BasicConfigurator;
import org.semanticweb.owl.validation.OWLValidationConstants;
import uk.ac.man.cs.img.owl.validation.SpeciesValidator;
import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
// import uk.ac.man.cs.img.owl.validation.ConstructChecker;
import org.xml.sax.SAXException;
import org.semanticweb.owl.util.URIMapper;
// import org.semanticweb.owl.util.PropertyBasedURIMapper;
// import java.util.Properties;
// import java.net.URISyntaxException;
// import java.io.FileInputStream;
// import java.io.IOException;
import aterm.*;
import aterm.pure.*;
import java.util.*;
import java.io.*;
// import javax.swing.filechooser.FileFilter;
import org.mindswap.pellet.owlapi.*;     // for PelletLoader
import org.mindswap.pellet.*;            // for KnowledgeBase

public class OWL2ATerm implements OWLValidationConstants {

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
			
			File file = new File("./output.term");
			if(file.exists()){
				file.delete();
				file.createNewFile();
			}
			
		
			// Warning
			List warningList;
			OWL2ATermErrorHandler handler = new OWL2ATermErrorHandler();

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
			
		    owlParserOutput(validation, warningList, onto).writeToSharedTextFile(new FileOutputStream(file));
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}

	
	static ATermList owlParserOutput(int valid, List message, OWLOntology ontology) {

		try {
			final String Lite = "Lite";
			final String Dl = "Dl";
			final String Full = "Full";
			PelletLoader ploader = new PelletLoader(new KnowledgeBase());
			ATermFactory factory = new PureFactory();
			// List atermList = new ArrayList();       // List of ATermAppl
			ATermList alist = factory.makeList();
			AFun validation = factory.makeAFun("mixer", 0, true);
			ATerm result;
			
			// Validation as ATerm appended in ATermList.
			switch (valid){
				case LITE:
					 validation = factory.makeAFun(Lite, 0, true);
					 break;
			    case DL: 
					 validation = factory.makeAFun(Dl, 0, true);
					 break;
			    case FULL: 
					 validation = factory.makeAFun(Full, 0, true);
					 break;
			}
			// atermList.add(factory.makeAppl(validation));
			alist = factory.makeList(factory.makeAppl(validation), alist);
			
			// Warning message
			for(Iterator it = message.iterator(); it.hasNext();){
				//atermList.add(factory.makeAppl(factory.makeAFun((String) it.next(), 0, true)));
				alist = factory.makeList(factory.makeAppl(factory.makeAFun((String) it.next(), 0, true)),alist);
			}
			
			// Load the current OWL ontology
			ploader.load(ontology);
			
			// Annotations
			// Set annotations = ontology.getAnnotations();
			
			// Axioms
			Set cas = ontology.getClassAxioms();
			Set ias = ontology.getIndividualAxioms();
			Set pas = ontology.getPropertyAxioms();
			
			/*
			if(annotations != null){
				for(Iterator aIt = annotations.iterator(); aIt.hasNext();){
					alist = factory.makeList(ploader.term((OWLAnnotationInstance) aIt.next()), alist);
				}
			}
			*/
			
			if(cas != null){
				for(Iterator classIt = cas.iterator(); classIt.hasNext();){
					// atermList.add(ploader.term((OWLClassAxiom) classIt.next()));
					alist = factory.makeList(ploader.term((OWLClassAxiom) classIt.next()), alist);
				}
			}
			
			if(ias != null){
				 for(Iterator indivIt = ias.iterator(); indivIt.hasNext();){
					// atermList.add(ploader.term((OWLIndividualAxiom) indivIt.next()));
				 	alist = factory.makeList(ploader.term((OWLIndividualAxiom) indivIt.next()), alist);
				 }
			}

			if(pas != null){
				for(Iterator propIt = pas.iterator(); propIt.hasNext();){
					// atermList.add(ploader.term((OWLPropertyAxiom) propIt.next()));
					alist = factory.makeList(ploader.term((OWLPropertyAxiom) propIt.next()), alist);
				}
			}

			/*
			ATerm[] atermArray = new ATerm[atermList.size()];
			
			int i = 0;
			for(Iterator it = atermList.iterator(); it.hasNext();){
				atermArray[i++] = (ATerm) it.next();
			}
			alist = ATermUtils.makeList(atermArray);
			*/
			
			// System.out.println(atermList.toString());
		    return alist.reverse();

		} catch (Exception e) {
			System.out.println(e);	
			return null;
		}
	}
}

class OWL2ATermErrorHandler implements OWLRDFErrorHandler {

	ArrayList wList;

	ArrayList eList;

	public OWL2ATermErrorHandler() {
		wList = new ArrayList();
		eList = new ArrayList();
	}

	public void owlFullConstruct(int code, String message) throws SAXException {
	}

	public void owlFullConstruct(int code, String message, Object obj)
			throws SAXException {
	}

	public void error(String message) throws SAXException {
		eList.add(message);
		// throw new SAXException();
	}

	public void warning(String message) throws SAXException {
		wList.add(message);
	}

	public List getList() {
		return wList;
	}

}