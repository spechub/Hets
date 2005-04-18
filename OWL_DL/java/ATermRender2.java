/**
 * Produces abstract syntax from OWL ontologies. 
 *
 *
 * Created: Fri Feb 21 09:12:03 2003
 *
 * @author Heng Jiang
 * @version $Id$
 */

// import java.io.PrintWriter;
import java.util.Set;
import java.util.List;
import java.util.Map;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLClass;
// import org.semanticweb.owl.impl.model.OWLPropertyImpl;
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
// import org.semanticweb.owl.io.owl_rdf.OWLRDFParser;
// import java.io.File;
// import java.io.FileOutputStream;
// import java.io.StringWriter;
import java.io.Writer;
import org.semanticweb.owl.model.helper.OntologyHelper;
import java.net.URISyntaxException;

import org.semanticweb.owl.model.OWLDataRange;
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
// import org.apache.log4j.BasicConfigurator;
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
// import org.semanticweb.owl.model.OWLDataRange;
import org.semanticweb.owl.model.OWLEnumeration;
import org.semanticweb.owl.io.ShortFormProvider;
import org.semanticweb.owl.io.abstract_syntax.*;          // for RenderingVisitor

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;
import aterm.AFun;
import aterm.pure.PureFactory;

public class ATermRender2 implements org.semanticweb.owl.io.Renderer,
		ShortFormProvider {

	Set allURIs;

	List shortNames;

	Map known;

	int reservedNames;

	RenderingVisitor visitor;

	String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
			"l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x",
			"y", "z", };

	static PureFactory factory = new PureFactory();

	ATermList emptyList = factory.makeList();
	
	AFun superFun = factory.makeAFun("Super", 1, false);
	AFun domainFun = factory.makeAFun("Domain", 1, false);
	AFun rangeFun = factory.makeAFun("Range", 1, false);
	AFun inverseOfFun = factory.makeAFun("InverseOf", 1, false);

	public ATermRender2(OWLOntology ontology) {
		// this.writer = new StringWriter();
		// this.pw = new PrintWriter(new StringWriter());
		visitor = new RenderingVisitor(this, ontology);
		try {
			allURIs = OntologyHelper.allURIs(ontology);
		} catch (Exception e) {
			System.out.println("Exception by constructor: ATermRender2:\n" + e);
		}
	}

	public void setOptions(Map map) {
	}

	public Map getOptions() {
		return null;
	}

	// visitor need not this method
	public void renderOntology(OWLOntology ontology, Writer writer)
			throws RendererException {

	}

	public ATermList renderClass(OWLOntology ontology, OWLClass clazz)
			throws OWLException {

		boolean done = false;
		ATermList resList = factory.makeList();
		AFun classFun = factory.makeAFun("Class", 5, false);
		ATermAppl classID = strToATermAppl("");
		ATermAppl dep = strToATermAppl("");
		ATermAppl mod = strToATermAppl("");
		ATermList annos = factory.makeList();
		ATermList descs = factory.makeList();

		if (clazz.getURI() != null) {
			classID = strToATermAppl(shortForm(clazz.getURI()));
			dep = strToATermAppl((clazz.isDeprecated(ontology) ? "true" : "false"));
		}

		/* Bit nasty this -- annotations result in a new axiom */
		if (!clazz.getAnnotations(ontology).isEmpty()) {
			annos = makeAnno(clazz.getAnnotations().iterator());
		}

		// Equivalent Class
		if (!clazz.getEquivalentClasses(ontology).isEmpty()) {

			mod = strToATermAppl("complete");

			for (Iterator it = clazz.getEquivalentClasses(ontology).iterator(); it
					.hasNext();) {
				OWLDescription eq = (OWLDescription) it.next();

				visitor.reset();
				eq.accept(visitor);

//				descs = factory.makeList(factory.makeAppl(factory.makeAFun(
//						mkOther(visitor.result()), 0, false)), descs);

				descs = factory.makeList(mkOther(visitor.result()), descs);
				done = true;
			}
			resList = factory.makeList(factory.makeAppl(classFun, classID, dep,
					mod, annos, descs.reverse()), resList);
		}

		if (!clazz.getSuperClasses(ontology).isEmpty()) {
			mod = strToATermAppl("partial");
			descs = factory.makeList();

			for (Iterator it = clazz.getSuperClasses(ontology).iterator(); it
					.hasNext();) {
				OWLDescription eq = (OWLDescription) it.next();
				visitor.reset();
				eq.accept(visitor);

//				descs = factory.makeList(factory.makeAppl(factory.makeAFun(
//						mkOther(visitor.result()), 0, false)), descs);
				descs = factory.makeList(mkOther(visitor.result()), descs);
				
				done = true;
			}
			resList = factory.makeList(factory.makeAppl(classFun, classID, dep,
					mod, annos, descs.reverse()), resList);
		}

		/*
		 * This has changed -- used to be simply a oneof in the class
		 * definition. We now get a special keyword in the vocabulary
		 */
		if (!clazz.getEnumerations(ontology).isEmpty()) {

			ATermList indivIDs = factory.makeList();
			// EnumeratedClass ClassID {Bool (True == deprecated)} [Annotation]
			// [IndividualID]
			AFun enumClass = factory.makeAFun("EnumeratedClass", 4, false);

			for (Iterator it = clazz.getEnumerations(ontology).iterator(); it
					.hasNext();) {

				OWLDescription eq = (OWLDescription) it.next();
				try {
					OWLEnumeration enumeration = (OWLEnumeration) eq;

					for (Iterator iit = enumeration.getIndividuals().iterator(); iit
							.hasNext();) {
						OWLIndividual ioe = (OWLIndividual) iit.next();
						visitor.reset();
						ioe.accept(visitor);

						indivIDs = factory.makeList(
								factory.makeAppl(factory.makeAFun(
										visitor.result(), 0, true)),
								indivIDs);
					}
					done = true;
				} catch (ClassCastException ex) {
					throw new RendererException(ex.getMessage());
				}
			}
			resList = factory.makeList(factory.makeAppl(enumClass, classID,
					dep, annos, indivIDs.reverse()), resList);
		}

		if (!done) {

			/* We need to give at least an empty definition */
			mod = strToATermAppl("partial");

			resList = factory.makeList(factory.makeAppl(classFun, classID, dep,
					mod, annos, factory.makeList()), resList);
		}

		// return is an ATermAppl: ATermOfClass(classID, ClassAxiomList)
		// AFun classAFun = factory.makeAFun("ATermOfClass", 2, false);
		return resList;
	}

	public ATermAppl renderIndividual(OWLOntology ontology, OWLIndividual ind)
			throws OWLException {

		// Individual (Maybe IndividualID) [Annotation] [Type] [Value]
		AFun indivFun = factory.makeAFun("Individual", 4, false);
		ATermAppl indivID = strToATermAppl(shortForm(ind.getURI()));
		ATermList annos = factory.makeList();
		ATermList types = factory.makeList();
		ATermList values = factory.makeList();
		AFun typeFun = factory.makeAFun("type", 1, false);
		AFun valueIndivFun = factory.makeAFun("valueIndiv", 2, false);
		AFun valueDLFun = factory.makeAFun("valueDL", 2, false);
		
		if (ind.isAnonymous()) {
			Map m = ind.getIncomingObjectPropertyValues(ontology);
			if (!m.isEmpty()) {
				indivID = strToATermAppl("_");
		//		return strToATermAppl("");
			}
		}
		// pw.print("Individual(" + shortForm(ind.getURI()));
		//	}
		if (ind.getAnnotations(ontology).isEmpty()
				&& ind.getTypes(ontology).isEmpty()
				&& ind.getObjectPropertyValues(ontology).keySet().isEmpty()
				&& ind.getDataPropertyValues(ontology).keySet().isEmpty()) {
			// pw.print(")");

			return factory.makeAppl(indivFun, indivID, emptyList, emptyList,
					emptyList);
		} else {

			annos = makeAnno(ind.getAnnotations(ontology).iterator());

			for (Iterator it = ind.getTypes(ontology).iterator(); it.hasNext();) {
				OWLDescription eq = (OWLDescription) it.next();
				
				visitor.reset();
				eq.accept(visitor);

				ATermAppl resType = factory.makeAppl(typeFun, mkOther(visitor.result()));
				types = factory.makeList(resType, types);
			}

			// recusive function call for "value IndividualvaluePropertyID Individual" can result in deadlock.
			// here is only "value IndivudualvaluePropertyID IndividualID" used.
			Map propertyValues = ind.getObjectPropertyValues(ontology);
			for (Iterator it = propertyValues.keySet().iterator(); it.hasNext();) {
				OWLObjectProperty prop = (OWLObjectProperty) it.next();
				Iterator valIt = ((Set) propertyValues.get(prop)).iterator();

				for (; valIt.hasNext();) {

					OWLIndividual oi = (OWLIndividual) valIt.next();
//					visitor.reset();
//					oi.accept(visitor);
//					ATermAppl resValue = factory.makeAppl(valueFun, propURI, strToATermAppl(mkOther(visitor.result())));
					
					ATermAppl propURI = strToATermAppl(shortForm(prop.getURI()));
// 					ATermAppl resValue = factory.makeAppl(valueIndivFun, propURI, renderIndividual(ontology,oi));
	
					AFun ivf = factory.makeAFun("IndividualID", 1, false);
					ATermAppl iv = factory.makeAppl(ivf, strToATermAppl(shortForm(oi.getURI())));
					ATermAppl resValue = factory.makeAppl(valueIndivFun, propURI, iv);
					values = factory.makeList(resValue, values);
				}
			}

			Map dataValues = ind.getDataPropertyValues(ontology);
			for (Iterator it = dataValues.keySet().iterator(); it.hasNext();) {
				OWLDataProperty prop = (OWLDataProperty) it.next();
				Set vals = (Set) dataValues.get(prop);

				Iterator valIt = vals.iterator();
				// if( valIt.hasNext()) pw.print(",");
				for (; valIt.hasNext();) {
					// valIt.next()).getURI());
					OWLDataValue dtv = (OWLDataValue) valIt.next();
					visitor.reset();
					dtv.accept(visitor);
					
					ATermAppl propURI = strToATermAppl(shortForm(prop.getURI()));
					ATermAppl resValue = factory.makeAppl(valueDLFun, propURI, mkOther(visitor.result()));
					values = factory.makeList(resValue, values);
					// pw.print(", value(" + shortForm(prop.getURI()) + ", "
					//		+ mkOther(visitor.result()) + ")");
					}
			}
			return factory.makeAppl(indivFun, indivID, annos, types, values);
		}
	}

	public ATermAppl renderAnnotationProperty(OWLOntology ontology,
			OWLAnnotationProperty prop) throws OWLException {

		// Writer writer = new StringWriter();
		// setWriter(writer);

		AFun apFun = factory.makeAFun("AnnotationProperty", 2, false);
		Set apSet = prop.getAnnotations();
		Iterator it = apSet.iterator();
		// Iterator it = OntologyHelper.getAnnotations(ontology, ontology ,prop).iterator();
		
		ATermList annoList = makeAnno(it);
		ATermAppl uri = strToATermAppl(shortForm(prop.getURI()));
		// pw.print("AnnotationProperty(" + shortForm(prop.getURI()) + ")");
		return factory.makeAppl(apFun, uri, annoList);
	}

	public ATermAppl renderObjectProperty(OWLOntology ontology,
			OWLObjectProperty prop) throws OWLException {

		// Writer writer = new StringWriter();
		// setWriter(writer);

		// ObjectProperty IndividualvaluedPropertyID
		//                Bool -- ^ True == deprecated
		//                [Annotation]
		//                [IndividualvaluedPropertyID] -- ^ super properties
		//                (Maybe IndividualvaluedPropertyID) -- ^ inverse of property
		//                Bool -- ^ True == symmetric
		//                (Maybe Func)
		//                [Description] -- ^ Domain
		//                [Description] -- ^ Range
		AFun opFun = factory.makeAFun("ObjectProperty", 9, false);
		ATermAppl indivID = strToATermAppl(shortForm(prop.getURI()));
		// pw.print("ObjectProperty(" + shortForm(prop.getURI()));

		ATermAppl function = strToATermAppl("");
		ATermAppl symmetric = strToATermAppl("");
		// AFun inverseOfFun = factory.makeAFun("InverseOf", 1, false);
		ATermAppl inverseOf = strToATermAppl("");
		// AFun superFun = factory.makeAFun("Super", 1, false);
		ATermList superList = emptyList;
		// AFun domainFun = factory.makeAFun("Domain", 1, false);
		ATermList domainList = emptyList;
		// AFun rangeFun = factory.makeAFun("Range", 1, false);
		ATermList rangeList = emptyList;
		ATermList annoList = emptyList;
		ATermAppl deprecated;

		// get annotations
		annoList = makeAnno(prop.getAnnotations().iterator());
		
		// maybe deprecated
		deprecated = prop.isDeprecated(ontology)? strToATermAppl("true"):strToATermAppl("false");

		// function
		if (prop.isTransitive(ontology)) {
			function = strToATermAppl("Transitive");
			// pw.print(", Transitive");
		}
		if (prop.isFunctional(ontology)) {
			function = strToATermAppl("Functional");
			// pw.print(", Functional");
		}
		if (prop.isInverseFunctional(ontology)) {
			function = strToATermAppl("InverseFunctional");
			// pw.print(", InverseFunctional");
		}
		if (prop.isSymmetric(ontology)) {
			symmetric = strToATermAppl("Symmetric");
			// pw.print(", Symmetric");
		}

		// only one inverseOf of ObjectProperty (see AS)
		for (Iterator it = prop.getInverses(ontology).iterator(); it.hasNext();) {

			OWLObjectProperty inv = (OWLObjectProperty) it.next();
			visitor.reset();
			inv.accept(visitor);

			inverseOf = factory.makeAppl(inverseOfFun,
					mkOther(visitor.result()));
			// pw.print(", inverseOf(" + mkOther(visitor.result()) + ")");
		}

		// a List of super property

		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {

			OWLObjectProperty sup = (OWLObjectProperty) it.next();
			visitor.reset();
			sup.accept(visitor);

			ATermAppl result = factory.makeAppl(superFun,
					mkOther(visitor.result()));
			superList = factory.makeList(result, superList);

			// pw.print(", super(" + mkOther(visitor.result()) + ")");
		}
		superList = superList.reverse();

		// a list of domain
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {

			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);

			ATermAppl result = factory.makeAppl(domainFun,
					mkOther(visitor.result()));
			domainList = factory.makeList(result, domainList);

			// pw.print(", domain(" + mkOther(visitor.result()) + ")");
			// 	    if (it.hasNext()) {
			// 		pw.print();
			// 	    }
		}
		domainList = domainList.reverse();

		// a list of range
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {

			OWLDescription ran = (OWLDescription) it.next();
			visitor.reset();
			ran.accept(visitor);

			ATermAppl result = factory.makeAppl(rangeFun,
					mkOther(visitor.result()));
			rangeList = factory.makeList(result, rangeList);
			// pw.print(", range(" + mkOther(visitor.result()) + ")");
		}
		rangeList = rangeList.reverse();

		// pw.print(")");
		// return writer.toString();
		ATerm[] aterms = { indivID, deprecated, annoList, superList, inverseOf,
				symmetric, function, domainList, rangeList };

		return factory.makeAppl(opFun, aterms);
	}

	public ATermAppl renderDataProperty(OWLOntology ontology, OWLDataProperty prop)
			throws OWLException {

//		Writer writer = new StringWriter();
//		setWriter(writer);
		//	DatatypeProperty  DatavaluedPropertyID 
        //                    Bool -- ^ True == deprecated  
        //					  [Annotation] 
        //					  [DatavaluedPropertyID]  -- ^ super properties 
        //					  (Maybe Func) 
        //					  [Description] -- ^ Domain 
        //				      [DataRange] -- ^ Range
		AFun dtpFun = factory.makeAFun("", 7, false);
		ATermAppl dvpID = strToATermAppl(shortForm(prop.getURI()));
		ATermList annoList = emptyList;
		ATermAppl deprecated = strToATermAppl("");
		ATermAppl functional = strToATermAppl("");
		ATermList superList = emptyList;
		ATermList domainList = emptyList;
		ATermList rangeList = emptyList;
	
		// pw.print("DatatypeProperty(" + shortForm(prop.getURI()));
		
		// get annotations
		for (Iterator it = prop.getAnnotations().iterator(); it.hasNext();) {
			annoList = makeAnno(it);
		}

		// maybe deprecated
		if (prop.isDeprecated(ontology)) {
			deprecated = strToATermAppl("Deprecated");
		}
		// maybe functional
		if (prop.isFunctional(ontology)) {
			//pw.print(", Functional");
			functional = strToATermAppl("Functional");
		}
		
		// a List of super property
		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {

			OWLObjectProperty sup = (OWLObjectProperty) it.next();
			visitor.reset();
			sup.accept(visitor);

			ATermAppl result = factory.makeAppl(superFun,
					mkOther(visitor.result()));
			superList = factory.makeList(result, superList);

			// pw.print(", super(" + mkOther(visitor.result()) + ")");
		}
		superList = superList.reverse();
		
		// a list of domain
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {

			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);

			ATermAppl result = factory.makeAppl(domainFun,
					mkOther(visitor.result()));
			domainList = factory.makeList(result, domainList);

			// pw.print(", domain(" + mkOther(visitor.result()) + ")");
			// 	    if (it.hasNext()) {
			// 		pw.print();
			// 	    }
		}
		domainList = domainList.reverse();

		// a list of range
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {

			OWLDataRange ran = (OWLDataRange) it.next();
			visitor.reset();
			ran.accept(visitor);

			ATermAppl result = factory.makeAppl(rangeFun,
					mkOther(visitor.result()));
			rangeList = factory.makeList(result, rangeList);
			// pw.print(", range(" + mkOther(visitor.result()) + ")");
		}
		rangeList = rangeList.reverse();
		
/* 
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {

			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);
			pw.print(", domain(" + mkOther(visitor.result()) + ")");
			// 	    if (it.hasNext()) {
			// 		pw.print();
			// 	    }
		}
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {

			OWLDataRange ran = (OWLDataRange) it.next();
			visitor.reset();
			ran.accept(visitor);
			pw.print(", range(" + mkOther(visitor.result()) + ")");
		}
*/

//		pw.print(")");
//		return writer.toString();

		return factory.makeAppl(dtpFun, dvpID, deprecated, annoList, superList, functional, domainList, rangeList);
		
	}

	public ATermAppl renderDataType(OWLOntology ontology, OWLDataType datatype)
			throws OWLException {

		// Writer writer = new StringWriter();
		// setWriter(writer);
		// pw.print("Datatype(" + shortForm(datatype.getURI()) + ")");
		return factory.makeAppl(factory.makeAFun("DataType", 1, false), strToATermAppl(shortForm(datatype.getURI())));

	}

	public ATermAppl renderClassAxiom(OWLClassAxiom axiom) throws OWLException {

		// Writer writer = new StringWriter();
		// setWriter(writer);

		visitor.reset();
		axiom.accept(visitor);

		// pw.print(mkOther(visitor.result()));
		// eturn writer.toString();
		if(visitor.result() == null) return strToATermAppl("");
		return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderPropertyAxiom(OWLPropertyAxiom axiom)
			throws OWLException {

//		Writer writer = new StringWriter();
//		setWriter(writer);
		visitor.reset();
		axiom.accept(visitor);

//		pw.print(mkOther(visitor.result()));
//		return writer.toString();
		if(visitor.result() == null) return strToATermAppl("");

		return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderIndividualAxiom(OWLIndividualAxiom axiom)
			throws OWLException {
//		Writer writer = new StringWriter();
//		setWriter(writer);

		visitor.reset();
		axiom.accept(visitor);
//		pw.print(mkOther(visitor.result()));
//		return writer.toString();
		// if(visitor.result() == null) return factory.makeAppl(factory.makeAFun("", 0, true));
		return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderAnnotationInstance(OWLOntology ontology, OWLAnnotationInstance instance)
		throws OWLException{
		
		URI aiID = instance.getProperty().getURI();
		return renderAnnotationContent(true, instance.getContent(), aiID.toString());
	}
	
	/* Well dodgy coding */
	public ATermAppl renderAnnotationContent(boolean isOntologyAnnotation, Object o, String annoID)
			throws OWLException {

		// Writer w = new StringWriter();
		// PrintWriter printW = new PrintWriter(w);
		ATermAppl aid = strToATermAppl(annoID);

		if(isOntologyAnnotation) {
			AFun defaltFun = factory.makeAFun("OntoAnnotation", 2, false);
			return factory.makeAppl(defaltFun, aid, strToATermAppl(o.toString()));
		}
		
		if (o instanceof URI) {
			AFun uriAnnoFun = factory.makeAFun("URIAnnotation", 2, false);
			ATerm uriA = strToATermAppl(o.toString());

			return factory.makeAppl(uriAnnoFun, aid, uriA);

		} else if (o instanceof OWLIndividual) {

			AFun indivFun = factory.makeAFun("IndivAnnotation", 2, false);
			ATerm indivA = strToATermAppl(((OWLIndividual) o).getURI().toString());

			return factory.makeAppl(indivFun, aid, indivA);

		} else if (o instanceof OWLDataValue) {

			AFun dlFun = factory.makeAFun("DLAnnotation", 2, false);

			OWLDataValue dv = (OWLDataValue) o;
			String result = escape(dv.getValue());

			URI dvdt = dv.getURI();
			String dvlang = dv.getLang();
			if (dvdt != null) {
				result += "^^" + dvdt; // ^^
			} else {
				if (dvlang != null) {
					result += "@" + dvlang;
				}
			}
			return factory.makeAppl(dlFun, aid, strToATermAppl(result));
		}else{
			throw(new OWLException("wrong object by calling the method of renderAnnotationContent."));
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

	public void generateShortNames() {
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

	public ATermAppl buildNamespaces() {
		/* Changed to fit with "concrete abstract syntax" */
		//	pw.print("[Namespaces: ");
		AFun nsFun1 = factory.makeAFun("Namespace", 1, false);
		AFun nsFun2 = factory.makeAFun("NS", 2, false);
		ATermList nsList = emptyList;
		// File file = new File("./namespaces.term");
//		
//		try{
//			if(file.exists()){
//				file.delete();
//				file.createNewFile();
//			}
//		}catch(Exception e){
//			System.out.println("Error: can not build file: namespaces.term.");
//			System.exit(1);
//		}
		
		// pw.print("Namespaces(");
		for (Iterator it = known.keySet().iterator(); it.hasNext();) {
			String ns = (String) it.next();
			ATermAppl nsA = strToATermAppl(ns);
			ATermAppl shrt = strToATermAppl((String) known.get(ns));
			nsList = factory.makeList(factory.makeAppl(nsFun2, shrt, nsA), nsList);
			// pw.print(" NS( " + shrt + ",\"<" + ns + ">\")");
		}
		for (int i = 0; i < shortNames.size(); i++) {
			if (i < names.length) {
				ATermAppl ns = strToATermAppl((String) shortNames.get(i));
				ATermAppl nl = strToATermAppl(names[i]);
				nsList = factory.makeList(factory.makeAppl(nsFun2, nl, ns), nsList);
				// pw.print(" NS( " + names[i] + ",\"<" + ns + ">\")");
			}
		}
//		
//		try{
//			ATermAppl result = factory.makeAppl(nsFun1, nsList.reverse());
//			result.writeToSharedTextFile(new FileOutputStream(file, true));
//		}catch(Exception e){
//			System.out.println("Exception by buildNamespeces: \t" + e);
//		}
		return factory.makeAppl(nsFun1, nsList.reverse());
	}

	public String shortForm(URI uri) {
		if (uri == null) {
			return "_";
		}
		try {
			if (uri.getFragment() == null || uri.getFragment().equals("")) {
				/* It's not of the form http://xyz/path#frag */
				return "<" + uri.toString() + ">";
			}
			/* It's of the form http://xyz/path#frag */
			String ssp = new URI(uri.getScheme(), uri.getSchemeSpecificPart(),
					null).toString();
			if (!ssp.endsWith("#")) {
				ssp = ssp + "#";
			}
			if (known.keySet().contains(ssp)) {
				// return factory.parse((String) known.get(ssp) + ":" + uri.getFragment()).toString();
				return (String) known.get(ssp) + "{" + uri.getFragment() + "}";
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
					// return factory.parse((names[shortNames.indexOf(ssp)]) + ":" + frag).toString();
					return names[shortNames.indexOf(ssp)] + "{" + frag + "}";
				}
				/* We can't shorten it -- there are too many... */
				return "<" + uri.toString() + ">";
			}
		} catch (URISyntaxException ex) {
			System.out.println("Exception by buiding an shortform of URI:" + ex);
		}
		return "<" + uri.toString() + ">";
	}

	// Return a collection, ordered by the URIs. 
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

	private ATerm mkOther(String term) {
		if (term == null || "".equals(term)) {
			return strToATermAppl("_");
		} else {
			String result = reduceComma(trag(term).trim().replace(' ', ','));
			try{
				return factory.parse(result);
			}catch(Exception e){
				return factory.parse("\"" + result + "\"");
			}
//			return reduceComma(trag(term).trim().replace(' ', ','));
		}
	}
	
	private String reduceComma(String str){
		StringBuffer sw = new StringBuffer();
		boolean hasComma = false;
		
		for(int i = 0; i < str.length(); i++){
			char c = str.charAt(i);
			if(!hasComma && c == ','){
				sw.append(c);
				hasComma = true;
			}else if(c == ','){
				continue;
			}else{
				sw.append(c);
				hasComma = false;
			}
		}
		return sw.toString();
	}

	/* for XML Language trag */
	private String trag(String str) {
		/* Should probably use regular expressions */
		StringBuffer sw = new StringBuffer();
		// String str = o.toString();
		boolean changed = false;
		for (int i = 0; i < str.length(); i++) {
			char c = str.charAt(i);
			if (c != '^' && c != '@') {
				sw.append(c);
			} else {
				if (sw.charAt(sw.length() - 1) == '"') {
					sw.deleteCharAt(sw.length() - 1);
					changed = true;
				}
				sw.append(c);
			}
		}
		if (changed)
			sw.append('"');
		return sw.toString();
	}

	private String handelDP(String term) {
		StringBuffer sw = new StringBuffer();
		for (int i = 0; i < term.length(); i++) {
			char c = term.charAt(i);
			if (c != ':') {
				sw.append(c);
			} else {
				for (int j = sw.length() - 1; j >= 0; j--) {
					if (sw.charAt(j) == ',' || sw.charAt(j) == '(') {
						sw.insert(j + 1, '"');
					}
				}
				sw.append(c);
			}
		}
		return sw.toString();
	}
/*
	private void setWriter(Writer writer) {
		this.pw = new PrintWriter(writer);
	}
*/
	private ATermList makeAnno(Iterator it) throws OWLException {

		// AFun annoFun = factory.makeAFun("Annotation", 2, false);
		ATermList annos = factory.makeList();
		ATermAppl annoCont;

		for (; it.hasNext();) {
			OWLAnnotationInstance oai = (OWLAnnotationInstance) it.next();

			annoCont = renderAnnotationContent(false, oai.getContent(), shortForm(oai
					.getProperty().getURI()));
			annos = factory.makeList(annoCont, annos);
			visitor.reset();
			oai.accept(visitor);
		}
		return annos.reverse();
	}
	

	public static ATermAppl strToATermAppl(String str) {
		return factory.makeAppl(factory.makeAFun(str, 0, true));
	}

} // Renderer
