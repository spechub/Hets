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
import org.semanticweb.owl.model.*; // Class Axiom
// import org.semanticweb.owl.io.simple.*;
// import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
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
// import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
import org.semanticweb.owl.validation.*;
// import uk.ac.man.cs.img.owl.validation.*;
// import org.xml.sax.SAXException;
import org.semanticweb.owl.util.URIMapper;
// import org.xml.sax.SAXException;
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
// import org.mindswap.pellet.owlapi.*; // for PelletLoader
import org.mindswap.pellet.*; // for KnowledgeBase
import org.mindswap.pellet.owlapi.PelletLoader;

public class OWL2ATerm implements OWLValidationConstants {

	static public void main(String[] args) {

		if (args.length != 1) {
			System.out.println("Usage: processor <URI>");
			System.exit(1);
		}

		String uriMapping = "";
		int validation = -1;
		ATermFactory factory = new PureFactory();
		OWLRDFParser rdfParser = null;
		Parser parser = null;
		OWLOntology onto = null;
		ATermList messageList;
		List warningList;


		// LongOpt[] longopts = new LongOpt[11];
		// boolean warnings = false;
		// boolean constructs = false;
		// boolean noImports = false;
		// BasicConfigurator.configure();

		try {
			SpeciesValidator sv = new SpeciesValidator();
			URI uri = new URI(args[0]);
			// URI uri = new URI("file:///D:/JOB/wine.xml");
			URIMapper mapper = null;

			/* Use the RDF Parser */
			rdfParser = new OWLRDFParser();

			File file = new File("./output.term");
			if (file.exists()) {
				file.delete();
				file.createNewFile();
			}

			System.out.println("OWL parse beginning ...");

			// Warning
			OWLToATermErrorHandler handler = new OWLToATermErrorHandler();
			rdfParser.setOWLRDFErrorHandler(handler);
			warningList = handler.getList();

			// call parser
			parser = rdfParser;
			parser.setConnection(OWLManager.getOWLConnection());
			if (mapper != null) {
				Map opt = new HashMap();
				opt.put("uriMapper", mapper);
				parser.setOptions(opt);
			}
			onto = parser.parseOntology(uri);

			/*
			 * Map options = new HashMap(); options.put("uriMapper", mapper); if
			 * (noImports) { options.put("ignoreSchemaImports", new
			 * Boolean(true)); } sv.setOptions(options);
			 */

			// build an new SpeciesValidatorReporter to save all messages.
			System.out.println("creating messages...");
			OWLATReporter reporter = new OWLATReporter();
			sv.setReporter(reporter);

			// Validation
			System.out.println("Please waiting ......");
			if (sv.isOWLLite(onto)) {
				validation = LITE;

			} else {
				System.out.println("Please waiting ......");
				if (sv.isOWLDL(onto)) {
					validation = DL;
				} else {
					System.out.println("Please waiting ......");
					if (sv.isOWLFull(onto)) {
						validation = FULL;
					}
				}
			}

			// concat messages and warning
			messageList = reporter.getMessageList();
			AFun warnFun = factory.makeAFun("ParseWarning", 1, false);
			AFun errFun = factory.makeAFun("ParseError", 1, false);
			for(Iterator it = warningList.iterator(); it.hasNext();){
				String currentMsg = (String) it.next();
				ATermAppl msgA = ATermRender2.strToATermAppl("");
				if(currentMsg.matches(".*\\s[Ee]rror.*")){
					msgA = factory.makeAppl(errFun, factory.parse(currentMsg));
				}else {
					msgA = factory.makeAppl(warnFun, ATermRender2.strToATermAppl(currentMsg));
				}
				messageList = factory.makeList(msgA, messageList);
			}
			
			owlParserOutput(validation, messageList, onto).
				writeToTextFile(new FileOutputStream(file, true));

//			owlParserOutput(validation, messageList, onto)
//					.writeToSharedTextFile(new FileOutputStream(file, true));
			System.out.println("Done!");
		} catch (IOException e) {
			System.out.println("Error: can not build file: output.term");
			System.exit(1);
		} catch (Exception ex) {
			System.out.println("OWL parse error: " + ex.getMessage());
			// System.out.println();
			// ex.printStackTrace();
		}
	}

	static ATermAppl owlParserOutput(int valid, ATermList messages,
			OWLOntology ontology) {

		try {
			final String AT_LITE = "Lite";
			final String AT_DL = "DL";
			final String AT_FULL = "Full";
			OWL2ATermLoader ploader = new OWL2ATermLoader(new KnowledgeBase(),
					ontology);
			ATermFactory factory = new PureFactory();
			// List atermList = new ArrayList(); // List of ATermAppl

			// ATerm for output:
			// OWLParserOutput(validation, messages, namespaces, ontology)
			AFun outputAFun = factory.makeAFun("OWLParserOutput", 4, false);
			ATermList alist = factory.makeList();
			AFun validation = factory.makeAFun("mixer", 0, true);
			// ATerm result;

			// Validation as ATerm appended in ATermList.
			switch (valid) {
			case LITE:
				validation = factory.makeAFun(AT_LITE, 0, true);
				break;
			case DL:
				validation = factory.makeAFun(AT_DL, 0, true);
				break;
			case FULL:
				validation = factory.makeAFun(AT_FULL, 0, true);
				break;
			}
			// atermList.add(factory.makeAppl(validation));
			ATermAppl validTerm = factory.makeAppl(validation);

			// Load the current OWL ontology
			// use an original PelletLoader to load current Ontology.
			System.out.println("creating ATermList from OWL.");
			PelletLoader loader = new PelletLoader(new KnowledgeBase());
			loader.load(ontology);
			ploader.setKB(loader.getKB());
			// Annotations
			// Set annotations = ontology.getAnnotations();

			// Classes
			Set classes = ontology.getClasses();
			// Class Axioms
			Set cas = ontology.getClassAxioms();
			// Individuals
			Set inds = ontology.getIndividuals();
			// Individual Axioms
			Set ias = ontology.getIndividualAxioms();
			// Property Axioms
			Set pas = ontology.getPropertyAxioms();
			// Annotation Properties
			Set aps = ontology.getAnnotationProperties();
			
			/*
			 * if(annotations != null){ for(Iterator aIt =
			 * annotations.iterator(); aIt.hasNext();){ alist =
			 * factory.makeList(ploader.term((OWLAnnotationInstance)
			 * aIt.next()), alist); } }
			 */

			// Classes
			if (classes != null) {
				for (Iterator classIt = classes.iterator(); classIt.hasNext();) {
					// atermList.add(ploader.term((OWLClassAxiom)
					// classIt.next()));
					alist = factory.makeList(ploader.term((OWLClass) classIt
							.next()), alist);
				}
			}
			
			// 	Class Axioms	
			if (cas != null) {
				for (Iterator caIt = cas.iterator(); caIt.hasNext();) {
					// atermList.add(ploader.term((OWLClassAxiom)
					// classIt.next()));
					alist = factory.makeList(ploader.term((OWLClassAxiom) caIt
							.next()), alist);
				}
			}

			
			// Annotation Properties
			if(aps != null){
				for(Iterator apIt = aps.iterator(); apIt.hasNext();){
					alist = factory.makeList(ploader.term((OWLAnnotationProperty) apIt.next()), alist);
				}
			}
			
			// Property Axioms
			if (pas != null) {
				for (Iterator propIt = pas.iterator(); propIt.hasNext();) {
					// atermList.add(ploader.term((OWLPropertyAxiom)
					// propIt.next()));
					alist = factory.makeList(ploader
							.term((OWLPropertyAxiom) propIt.next()), alist);
				}
			}
			
			// Individual Axioms
			if (ias != null) {
				for (Iterator indivIt = ias.iterator(); indivIt.hasNext();) {
					// atermList.add(ploader.term((OWLIndividualAxiom)
					// indivIt.next()));
					alist = factory.makeList(ploader
							.term((OWLIndividualAxiom) indivIt.next()), alist);
				}
			}
			
			if(inds != null){
				for(Iterator indIt = inds.iterator(); indIt.hasNext();){
					alist = factory.makeList(ploader.term((OWLIndividual) indIt.next()), alist);
				}
			}
			
			// System.out.println(atermList.toString());
			return factory.makeAppl(outputAFun, validTerm, messages, ploader
					.getNamespace(), alist.reverse());

		} catch (Exception e) {
			System.out.println("Exception by owlParserOutput: \n" + e);
			return null;
		}
	}
}

/**
 * 
 * @author Jiang
 *
 * This is a errorhandler of OWLParser that creat a ATermList of errors and warnings.
 */
/*
class OWL2ATermErrorHandler implements OWLRDFErrorHandler {

	ATermList eList;

	ATermList wList;

	private PureFactory factory = new PureFactory();
	
	public OWL2ATermErrorHandler() {
		wList = factory.makeList();
		eList = factory.makeList();
	}

	public void error(String message) throws SAXException {
		AFun errFun = factory.makeAFun("ParserError", 1, false);
		ATermAppl err = factory.makeAppl(errFun, factory.parse(message));
		eList = factory.makeList(err, eList); 
		throw new SAXException();
	}

	public ATermList getList() {
		return wList.concat(eList);
	}

	public void owlFullConstruct(int code, String message) throws SAXException {
	}

	public void owlFullConstruct(int code, String message, Object obj)
			throws SAXException {
	}

	public void warning(String message) throws SAXException {
		AFun warnFun = factory.makeAFun("ParseWarning", 1, false);
		ATermAppl warn = factory.makeAppl(warnFun, factory.parse(message));
		wList = factory.makeList(warn, wList); 
	}
}
*/


class OWLATReporter implements SpeciesValidatorReporter, OWLValidationConstants {

	static ATermFactory factory = new PureFactory();

	static ATermList messageList = factory.makeList();

	// File file;
	AFun messageFun = factory.makeAFun("MassageList", 1, false);

	public OWLATReporter() {
		// factory = new PureFactory();
		// messageList = factory.makeList();
		// file = new File("./output.term");
	}

	public void done(String str) {

	}

	public void explain(int l, int code, String str) {

		// System.out.println(SpeciesValidator.readableCode( code ));

		ATermAppl aa = factory.makeAppl(factory.makeAFun("Message", 3, false),
				factory.parse(level(l)), factory.parse("\""
						+ SpeciesValidator.readableCode(code) + "\""), factory
						.parse("\"" + str + "\""));
		messageList = factory.makeList(aa, messageList);

		/*
		 * try{ aa.writeToSharedTextFile(new FileOutputStream(file, true));
		 * }catch(Exception e){ System.out.println(e); }
		 */
		// System.out.println(aa);
	}

	public ATermList getMessageList() {
		return messageList.reverse();
	}

	private String level(int l) {
		if (l == LITE) {
			return "OWL-Lite";
		} else if (l == DL) {
			return "OWL-DL  ";
		} else if (l == FULL) {
			return "OWL-Full";
		} else {
			return "OTHER   ";
		}
	}

	public void message(String str) {

	}

	public void ontology(OWLOntology onto) {

	}
}
