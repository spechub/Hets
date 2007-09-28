/**
 * Produces abstract syntax from OWL ontologies. 
 *
 *
 * Created: Fri Feb 21 09:12:03 2003
 *
 * @author Heng Jiang
 * @version $Id$
 */

import java.io.PrintWriter;
import java.util.Set;
import java.util.List;
import java.util.Map;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.io.vocabulary.OWLVocabularyAdapter;
import org.semanticweb.owl.io.vocabulary.RDFVocabularyAdapter;
import org.semanticweb.owl.io.vocabulary.RDFSVocabularyAdapter;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.Iterator;
import java.net.URI;
import org.semanticweb.owl.io.RendererException;
// import org.semanticweb.owl.util.OWLConnection;
// import org.semanticweb.owl.util.OWLManager;
//import org.semanticweb.owl.io.owl_rdf.OWLRDFParser;
import java.io.StringWriter;
import java.io.Writer;
import org.semanticweb.owl.model.helper.OntologyHelper;
import java.net.URISyntaxException;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLIndividual;
import org.semanticweb.owl.model.OWLObjectProperty;
import org.semanticweb.owl.model.OWLAnnotationProperty;
import org.semanticweb.owl.model.OWLDataProperty;
import java.util.TreeSet;
import java.util.Comparator;
import java.util.SortedSet;
import org.semanticweb.owl.model.OWLEntity;
import org.semanticweb.owl.model.OWLClassAxiom;
import org.semanticweb.owl.model.OWLDescription;
import org.apache.log4j.BasicConfigurator;
// import org.semanticweb.owl.model.OWLObjectPropertyInstance;
import org.semanticweb.owl.model.OWLDataValue;
import org.semanticweb.owl.model.OWLIndividualAxiom;
import org.semanticweb.owl.model.OWLDataType;
import org.semanticweb.owl.model.OWLAnnotationInstance;
import org.semanticweb.owl.io.vocabulary.XMLSchemaSimpleDatatypeVocabulary;
// import org.semanticweb.owl.io.vocabulary.OWLVocabularyAdapter;
// import org.semanticweb.owl.io.vocabulary.RDFSVocabularyAdapter;
import org.semanticweb.owl.model.OWLPropertyAxiom;
// import java.util.HashSet;
import org.semanticweb.owl.model.OWLDataRange;
import org.semanticweb.owl.model.OWLEnumeration;
import org.semanticweb.owl.io.ShortFormProvider;
import org.semanticweb.owl.io.abstract_syntax.*;

public class Renderer2 implements org.semanticweb.owl.io.Renderer,
		ShortFormProvider {

	/*
	 * NOTE: This renderer isn't very careful about where assertions come from,
	 * so *all* information about classes, properties etc. is rendered.
	 */

	private PrintWriter pw;

	private Set allURIs;

	private List shortNames;

	private Map known;

	private int reservedNames;

	private RenderingVisitor visitor;

	private String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i",
			"j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v",
			"w", "x", "y", "z", };

	public Renderer2() {
	}

	public void setOptions(Map map) {
	}

	public Map getOptions() {
		return null;
	}

	public void renderOntology(OWLOntology ontology, Writer writer)
			throws RendererException {
		try {
			this.pw = new PrintWriter(writer);
			this.allURIs = OntologyHelper.allURIs(ontology);
			this.visitor = new RenderingVisitor(this, ontology);
			generateShortNames();
			pw.println();
			/* Print the ontology's logical URI */
			pw.println("Ontology( "  + shortForm(ontology.getURI()));
			/* Namespaces */
			writeNamespaces();
			
			pw.println();
			boolean done = false;

			for (Iterator it = ontology.getIncludedOntologies().iterator(); it
					.hasNext();) {
				/* Use the physical URI here.... */
				pw.println(", Annotation( owl:imports" + ", \""
						+ ((OWLOntology) it.next()).getPhysicalURI() + "\")");
				done = true;
			}
			if (done) {
				pw.println();
			}

			if (!ontology.getAnnotations(ontology).isEmpty()) {
				for (Iterator it = ontology.getAnnotations(ontology).iterator(); it
						.hasNext();) {
					OWLAnnotationInstance oai = (OWLAnnotationInstance) it
							.next();
					pw.print(", Annotation("
							+ shortForm(oai.getProperty().getURI()));
					/* Just whack out the content */
					renderAnnotationContent(oai.getContent());
					//		    pw.print( "\"" + oai.getContent() + "\"" );
					pw.println(")");
					visitor.reset();
					oai.accept(visitor);
				}
				done = true;
			}
			if (done) {
				pw.println();
			}

			/* Moved properties to the top. Makes parsing easier. */

			done = false;
			for (Iterator it = orderedEntities(ontology.getObjectProperties())
					.iterator(); it.hasNext();) {
				done = true;
				renderObjectProperty(ontology, (OWLObjectProperty) it.next());
			}
			//	    pw.println("/* Data Properties */");
			if (done) {
				pw.println();
			}
			done = false;
			for (Iterator it = orderedEntities(ontology.getDataProperties())
					.iterator(); it.hasNext();) {
				done = true;
				renderDataProperty(ontology, (OWLDataProperty) it.next());
			}
			if (done) {
				pw.println();
			}

			done = false;
			for (Iterator it = orderedEntities(ontology.getClasses())
					.iterator(); it.hasNext();) {
				done = true;
				renderClass(ontology, (OWLClass) it.next());
			}
			//	    pw.println("/* Annotation Properties */");
			if (done) {
				pw.println();
			}
			done = false;
			for (Iterator it = orderedEntities(
					ontology.getAnnotationProperties()).iterator(); it
					.hasNext();) {
				OWLAnnotationProperty prop = (OWLAnnotationProperty) it.next();
				/* Write them out even if they're built in. */
				done = true;
				renderAnnotationProperty(ontology, prop);

				// 		if (
				// !OWLVocabularyAdapter.INSTANCE.getAnnotationProperties().contains(
				// prop.getURI().toString() ) ) {
				// 		    done = true;
				// 		    renderAnnotationProperty( ontology, prop );
				// 		}
			}
			//	    pw.println("/* Object Properties */");
			if (done) {
				pw.println();
			}
			done = false;
			for (Iterator it = orderedEntities(ontology.getIndividuals())
					.iterator(); it.hasNext();) {
				done = true;
				renderIndividual(ontology, (OWLIndividual) it.next());
			}
			//	    pw.println("/* Class Axioms */");
			if (done) {
				pw.println();
			}
			done = false;

			for (Iterator it = orderedEntities(ontology.getDatatypes())
					.iterator(); it.hasNext();) {
				done = true;
				renderDataType(ontology, (OWLDataType) it.next());
			}
			//	    pw.println("/* Object Properties */");
			if (done) {
				pw.println();
			}
			done = false;

			for (Iterator it = orderedEntities(ontology.getClassAxioms())
					.iterator(); it.hasNext();) {
				done = true;
				renderClassAxiom((OWLClassAxiom) it.next());
			}
			//	    pw.println("/* Individual Axioms */");
			if (done) {
				pw.println();
			}
			done = false;
			for (Iterator it = orderedEntities(ontology.getPropertyAxioms())
					.iterator(); it.hasNext();) {
				done = true;
				renderPropertyAxiom((OWLPropertyAxiom) it.next());
			}
			if (done) {
				pw.println();
			}
			done = false;
			for (Iterator it = orderedEntities(ontology.getIndividualAxioms())
					.iterator(); it.hasNext();) {
				done = true;
				renderIndividualAxiom((OWLIndividualAxiom) it.next());
			}
			if (done) {
				pw.println();
			}
			
			pw.println(")");

		} catch (OWLException ex) {
			throw new RendererException(ex.getMessage());
		}
	}

	private void renderClass(OWLOntology ontology, OWLClass clazz)
			throws OWLException {
		boolean done = false;
		for (Iterator it = clazz.getEquivalentClasses(ontology).iterator(); it
				.hasNext();) {
			OWLDescription eq = (OWLDescription) it.next();
			pw.println(", Class(" + shortForm(clazz.getURI()) + ","
					+ (clazz.isDeprecated(ontology) ? " Deprecated," : "")
					+ " complete, ");
			visitor.reset();
			eq.accept(visitor);
			pw.println("  " + mkOther(visitor.result()) + ")");
			done = true;
		}

		if (!clazz.getSuperClasses(ontology).isEmpty()) {
			pw.println(", Class(" + shortForm(clazz.getURI()) + ","
					+ (clazz.isDeprecated(ontology) ? " Deprecated," : "")
					+ " partial ");

			for (Iterator it = clazz.getSuperClasses(ontology).iterator(); it
					.hasNext();) {
				OWLDescription eq = (OWLDescription) it.next();
				visitor.reset();
				eq.accept(visitor);
				pw.print(", " + mkOther(visitor.result()));
				if (it.hasNext()) {
					pw.println();
				}
				done = true;
			}
			pw.println(")");
		}
		/*
		 * This has changed -- used to be simply a oneof in the class
		 * definition. We now get a special keyword in the vocabulary
		 */
		for (Iterator it = clazz.getEnumerations(ontology).iterator(); it
				.hasNext();) {
			OWLDescription eq = (OWLDescription) it.next();
			pw.print(", EnumeratedClass(" + shortForm(clazz.getURI())
					+ (clazz.isDeprecated(ontology) ? ", Deprecated" : ""));
			/* We know that the description has to be a oneof */
			try {
				OWLEnumeration enumeration = (OWLEnumeration) eq;

				for (Iterator iit = enumeration.getIndividuals().iterator(); iit
						.hasNext();) {
					OWLIndividual desc = (OWLIndividual) iit.next();
					visitor.reset();
					desc.accept(visitor);
					pw.print(", " + mkOther(visitor.result()));
					// 		    if (iit.hasNext()) {
					// 			pw.print(" ");
					// 		    }
				}
				pw.println(")");
				done = true;
			} catch (ClassCastException ex) {
				throw new RendererException(ex.getMessage());
			}
		}
		/* Bit nasty this -- annotations result in a new axiom */
		if (!clazz.getAnnotations(ontology).isEmpty()) {
			pw.println(", Class(" + shortForm(clazz.getURI()) + ","
					+ " partial ");
			for (Iterator it = clazz.getAnnotations(ontology).iterator(); it
					.hasNext();) {
				OWLAnnotationInstance oai = (OWLAnnotationInstance) it.next();
				pw.print(", annotation("
						+ shortForm(oai.getProperty().getURI()));
				/* Just whack out the content. This isn't quite right... */
				renderAnnotationContent(oai.getContent());
				//		pw.print( "\"" + oai.getContent() + "\"" );
				pw.println(")");
				/* Do we need to do this??? */
				visitor.reset();
				oai.accept(visitor);
				// 		if (it.hasNext()) {
				// 		    pw.println();
				// 		}
			}
			pw.println(")");
			done = true;
		}
		if (!done) {
			/* We need to give at least an empty definition */
			pw.println(", Class(" + shortForm(clazz.getURI()) + ","
					+ (clazz.isDeprecated(ontology) ? " Deprecated," : "")
					+ " partial" + ")");
		}
	}

	private void renderIndividual(OWLOntology ontology, OWLIndividual ind)
			throws OWLException {
		/*
		 * If the individual is anonymous and has any incoming properties, then
		 * we do not wish to show it here -- it will be rendered during the
		 * rendering of the thing that points to it.
		 */
		if (ind.isAnonymous()) {
			Map m = ind.getIncomingObjectPropertyValues(ontology);
			if (!m.isEmpty()) {
				return;
			}
		}
		// 	if ( ind.isAnonymous() ) {
		// 	    pw.print(" Individual(" );
		// 	} else {
		pw.print(", Individual(" + shortForm(ind.getURI()));
		//	}
		if (ind.getAnnotations(ontology).isEmpty()
				&& ind.getTypes(ontology).isEmpty()
				&& ind.getObjectPropertyValues(ontology).keySet().isEmpty()
				&& ind.getDataPropertyValues(ontology).keySet().isEmpty()) {
			pw.println(")");
		} else {
			// pw.println(", ");
			for (Iterator it = ind.getAnnotations(ontology).iterator(); it
					.hasNext();) {
				pw.println();
				OWLAnnotationInstance oai = (OWLAnnotationInstance) it.next();
				pw.print(", annotation("
						+ shortForm(oai.getProperty().getURI()));
				/* Just whack out the content */
				renderAnnotationContent(oai.getContent());
				//		pw.print( oai.getContent() );
				pw.println(")");
				visitor.reset();
				oai.accept(visitor);
				// 		if (it.hasNext()) {
				// 		    pw.println();
				// 		}
			}

			//	    pw.println();
			for (Iterator it = ind.getTypes(ontology).iterator(); it.hasNext();) {
				pw.println();
				OWLDescription eq = (OWLDescription) it.next();
				visitor.reset();
				eq.accept(visitor);
				pw.print(", type(" + mkOther(visitor.result()) + ")");
				// if (it.hasNext()) {
				//     pw.print(",");
				// }else break;
			}
			Map propertyValues = ind.getObjectPropertyValues(ontology);
			//	    System.out.println("ZZ: " + ind.getURI());
			for (Iterator it = propertyValues.keySet().iterator(); it.hasNext();) {
				pw.println();
				OWLObjectProperty prop = (OWLObjectProperty) it.next();
				Iterator valIt = ((Set) propertyValues.get(prop)).iterator();
				// if( valIt.hasNext()) pw.print(",");
				for (; valIt.hasNext();) {
					//		    System.out.println("QQ: " + ((OWLIndividual)
					// valIt.next()).getURI());
					OWLIndividual oi = (OWLIndividual) valIt.next();
					visitor.reset();
					oi.accept(visitor);
					pw.print(", value(" + shortForm(prop.getURI()) + ", "
							+ mkOther(visitor.result()) + ")");
					//if (valIt.hasNext()) {
					//    pw.print(",");
					//    pw.println();
					//}else break;
				}
				// 		if (it.hasNext()) {
				// 		    pw.println();
				// 		}
			}
			Map dataValues = ind.getDataPropertyValues(ontology);
			//	    System.out.println("ZZ: " + ind.getURI());
			for (Iterator it = dataValues.keySet().iterator(); it.hasNext();) {
				pw.println();
				OWLDataProperty prop = (OWLDataProperty) it.next();
				Set vals = (Set) dataValues.get(prop);

				Iterator valIt = vals.iterator();
				// if( valIt.hasNext()) pw.print(",");
				for (; valIt.hasNext();) {
					//		    System.out.println("QQ: " + ((OWLIndividual)
					// valIt.next()).getURI());
					OWLDataValue dtv = (OWLDataValue) valIt.next();
					visitor.reset();
					dtv.accept(visitor);
					pw.print(", value(" + shortForm(prop.getURI()) + ", "
							+ mkOther(visitor.result()) + ")");
					// if (valIt.hasNext()) {
					//	pw.print(",");
					//	pw.println();
					// }else break;
				}
				// 		if (it.hasNext()) {
				// 		    pw.println();
				// 		}
			}
			pw.println(")");
		}

	}

	private void renderAnnotationProperty(OWLOntology ontology,
			OWLAnnotationProperty prop) throws OWLException {
		pw.println(", AnnotationProperty(" + shortForm(prop.getURI()) + ")");
	}

	private void renderObjectProperty(OWLOntology ontology,
			OWLObjectProperty prop) throws OWLException {
		pw.print(", ObjectProperty(" + shortForm(prop.getURI()));
		if (prop.isTransitive(ontology)) {
			pw.print(", Transitive");
		}
		if (prop.isFunctional(ontology)) {
			pw.print(", Functional");
		}
		if (prop.isInverseFunctional(ontology)) {
			pw.print(", InverseFunctional");
		}
		if (prop.isSymmetric(ontology)) {
			pw.print(", Symmetric");
		}
		for (Iterator it = prop.getInverses(ontology).iterator(); it.hasNext();) {
			pw.println();
			OWLObjectProperty inv = (OWLObjectProperty) it.next();
			visitor.reset();
			inv.accept(visitor);
			pw.print(", inverseOf(" + mkOther(visitor.result()) + ")");
		}
		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {
			pw.println();
			OWLObjectProperty sup = (OWLObjectProperty) it.next();
			visitor.reset();
			sup.accept(visitor);
			pw.print(", super(" + mkOther(visitor.result()) + ")");
		}
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {
			pw.println();
			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);
			pw.print(", domain(" + mkOther(visitor.result()) + ")");
			// 	    if (it.hasNext()) {
			// 		pw.println();
			// 	    }
		}
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {
			pw.println();
			OWLDescription ran = (OWLDescription) it.next();
			visitor.reset();
			ran.accept(visitor);
			pw.print(", range(" + mkOther(visitor.result()) + ")");
		}

		pw.println(")");
	}

	private void renderDataProperty(OWLOntology ontology, OWLDataProperty prop)
			throws OWLException {
		pw.print(", DatatypeProperty(" + shortForm(prop.getURI()));
		if (prop.isFunctional(ontology)) {
			pw.print(", Functional");
		}

		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {
			pw.println();
			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);
			pw.print(", domain(" + mkOther(visitor.result()) + ")");
			// 	    if (it.hasNext()) {
			// 		pw.println();
			// 	    }
		}
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {
			pw.println();
			OWLDataRange ran = (OWLDataRange) it.next();
			visitor.reset();
			ran.accept(visitor);
			pw.print(", range(" + mkOther(visitor.result()) + ")");
		}

		pw.println(")");

	}

	private void renderDataType(OWLOntology ontology, OWLDataType datatype)
			throws OWLException {
		pw.println(", Datatype(" + shortForm(datatype.getURI()) + ")");
	}

	private void renderClassAxiom(OWLClassAxiom axiom) throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		pw.println(", " + mkOther(visitor.result()));
	}

	private void renderPropertyAxiom(OWLPropertyAxiom axiom)
			throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		pw.println(", " + mkOther(visitor.result()));
	}

	private void renderIndividualAxiom(OWLIndividualAxiom axiom)
			throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		pw.println(", " + mkOther(visitor.result()));
	}

	/* Well dodgy coding */
	private void renderAnnotationContent(Object o) throws OWLException {
		if (o instanceof URI) {
			pw.print("," + o.toString()); //   pw.print( "\"" + o.toString() +"\"");
		} else if (o instanceof OWLIndividual) {
			pw.print("," + ((OWLIndividual) o).getURI().toString());
		} else if (o instanceof OWLDataValue) {
			OWLDataValue dv = (OWLDataValue) o;
			pw.print(", \"" + escape(dv.getValue()));
			/* Only show it if it's not string */
			URI dvdt = dv.getURI();
			String dvlang = dv.getLang();
			if (dvdt != null) {
				pw.print("^^" + dvdt + "\""); // ^^
			} else {
				if (dvlang != null) {
					pw.print("@" + dvlang + "\"");
				} else
					pw.print("\"");
			}
		} else {
			pw.print(o.toString());
		}
	}

	/* Replace " with \" and \ with \\ */
	public static String escape(Object o) {
		/* Should probably use regular expressions */
		StringBuffer sw = new StringBuffer();
		String str = o.toString();
		for (int i = 0; i < str.length(); i++) {
			char c = str.charAt(i);
			if (c != '"' && c != '\\') {
				sw.append(c);
			} else {
				sw.append('\\');
				sw.append(c);
			}
		}
		return sw.toString();
	}

	private void generateShortNames() {
		/* Generates a list of namespaces. */
		shortNames = new ArrayList();
		known = new HashMap();
		known.put(OWLVocabularyAdapter.INSTANCE.OWL, "owl");
		known.put(RDFVocabularyAdapter.INSTANCE.RDF, "rdf");
		known.put(RDFSVocabularyAdapter.INSTANCE.RDFS, "rdfs");
		known.put(XMLSchemaSimpleDatatypeVocabulary.INSTANCE.XS, "xsd");

		for (Iterator it = allURIs.iterator(); it.hasNext();) {
			try {
				URI uri = (URI) it.next();
				if (uri.getFragment() != null) {
					String ssp = new URI(uri.getScheme(), uri
							.getSchemeSpecificPart(), null).toString();
					/* Trim off the fragment bit if necessary */
					if (!ssp.endsWith("#")) {
						ssp = ssp + "#";
					}
					if (!known.keySet().contains(ssp)
							&& !shortNames.contains(ssp)) {
						shortNames.add(ssp);
					}
				}
			} catch (URISyntaxException ex) {
			}
		}
	}

	private void writeNamespaces() {
		/* Changed to fit with "concrete abstract syntax" */
		//	pw.println("[Namespaces: ");
		boolean first = true;
		pw.print(", Namespaces(");
		for (Iterator it = known.keySet().iterator(); it.hasNext();) {
			String ns = (String) it.next();
			String shrt = (String) known.get(ns);
			if(first) {
				pw.println(" NS( " + shrt + ",\"<" + ns + ">\")");
				first = false;
			}
			pw.println("\t\t  , NS( " + shrt + ",\"<" + ns + ">\")");
		}
		for (int i = 0; i < shortNames.size(); i++) {
			if (i < names.length) {
				String ns = (String) shortNames.get(i);
				if(first) {
					pw.println(" NS( " + names[i] + ",\"<" + ns + ">\")");
					first = false;
				}
				pw.println("\t\t  , NS( " + names[i] + ",\"<" + ns + ">\")");
			}
		}
		pw.println("\t\t  )");
	}

	public String shortForm(URI uri) {
		if (uri == null) {
			return "_";
		}
		try {
			if (uri.getFragment() == null || uri.getFragment().equals("")) {
				/* It's not of the form http://xyz/path#frag */
				return "\"" + "<" + uri.toString() + ">" + "\"";
			}
			/* It's of the form http://xyz/path#frag */
			String ssp = new URI(uri.getScheme(), uri.getSchemeSpecificPart(),
					null).toString();
			if (!ssp.endsWith("#")) {
				ssp = ssp + "#";
			}
			if (known.keySet().contains(ssp)) {
				return (String) known.get(ssp) + ":" + uri.getFragment();
			}
			if (shortNames.contains(ssp)) {
				/*
				 * Check whether the fragment is ok, e.g. just contains letters.
				 */
				String frag = uri.getFragment();
				boolean fragOk = true;
				/*
				 * This is actually quite severe -- URIs allow other stuff in
				 * here, but for our concrete syntax we don't, only letters,
				 * numbers and _
				 */
				for (int i = 0; i < frag.length(); i++) {
					fragOk = fragOk
							&& (Character.isLetter(frag.charAt(i))
									|| Character.isDigit(frag.charAt(i)) || frag
									.charAt(i) == '_');
				}
				if (fragOk && (shortNames.indexOf(ssp)) < names.length) {
					return (names[shortNames.indexOf(ssp)]) + ":" + frag;
				}
				/* We can't shorten it -- there are too many... */
				return "<" + uri.toString() + ">";
			}
		} catch (URISyntaxException ex) {
		}
		return "<" + uri.toString() + ">";
	}

	/* Return a collection, ordered by the URIs. */
	private SortedSet orderedEntities(Set entities) {
		SortedSet ss = new TreeSet(new Comparator() {
			public int compare(Object o1, Object o2) {
				try {
					return ((OWLEntity) o1).getURI().toString().compareTo(
							((OWLEntity) o2).getURI().toString());
				} catch (Exception ex) {
					return o1.toString().compareTo(o2.toString());
				}
			}
		});
		ss.addAll(entities);
		return ss;
	}

	private String mkOther(String term) {
		if (term == null) {
			return "";
		} else {
			return trag(term).trim().replace(' ', ',');
		}
	}

	/* for XML Language trag */
	private String trag(String o) {
		/* Should probably use regular expressions */
		StringBuffer sw = new StringBuffer();
		String str = o.toString();
		boolean changed = false;
		for (int i = 0; i < str.length(); i++) {
			char c = str.charAt(i);
			if (c != '^' && c != '@') {
				sw.append(c);
			} else {
				if(sw.charAt(sw.length()-1) == '"'){
					sw.deleteCharAt(sw.length()-1);
					changed = true;
				}
				sw.append(c);
			}
		}
		if(changed) sw.append('"');
		return sw.toString();
	}

	
	public static void main(String[] args) {
		try {
			BasicConfigurator.configure();

			URI uri = new URI(args[0]);

			OWLOntology onto = OntologyHelper.getOntology(uri);
			Renderer2 renderer = new Renderer2();
			Writer writer = new StringWriter();
			renderer.renderOntology(onto, writer);
			System.out.println(writer.toString());
		} catch (Exception ex) {
			ex.printStackTrace();
		}
	}

} // Renderer
