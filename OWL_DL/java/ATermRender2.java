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
import org.semanticweb.owl.model.OWLObject;
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
import org.semanticweb.owl.io.abstract_syntax.*; // for RenderingVisitor

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

	RenderingVisitor2 visitor;

	String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
			"l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x",
			"y", "z", };

	static PureFactory factory = new PureFactory();

	ATermList emptyList = factory.makeList();

	AFun axFun = factory.makeAFun("Ax", 1, false);

	AFun fcFun = factory.makeAFun("Fc", 1, false);

	AFun annoFun = factory.makeAFun("Anno", 1, false);

	AFun superFun = factory.makeAFun("Super", 1, false);

	// AFun domainFun = factory.makeAFun("Domain", 1, false);

	// gAFun rangeFun = factory.makeAFun("Range", 1, false);

	// AFun inverseOfFun = factory.makeAFun("InverseOf", 1, false);

	AFun justFun = factory.makeAFun("Just", 1, false);

	public ATermRender2(OWLOntology ontology) {
		// this.writer = new StringWriter();
		// this.pw = new PrintWriter(new StringWriter());
		visitor = new RenderingVisitor2(this, ontology);
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
			dep = strToATermAppl1((clazz.isDeprecated(ontology) ? "true"
					: "false"));
		}

		
		/* Bit nasty this -- annotations result in a new axiom */
		if (!clazz.getAnnotations(ontology).isEmpty()) {
			annos = makeAnno(clazz.getAnnotations().iterator());
		}

		// Equivalent Class
		if (!clazz.getEquivalentClasses(ontology).isEmpty()) {

			mod = strToATermAppl1("Complete");

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
			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(classFun, classID, dep, mod, annos, descs
							.reverse())), resList);
		}

		if (!clazz.getSuperClasses(ontology).isEmpty()) {
			mod = strToATermAppl1("Partial");
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
			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(classFun, classID, dep, mod, annos, descs
							.reverse())), resList);
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

						indivIDs = factory.makeList(factory.makeAppl(factory.makeAFun(visitor
										.result(), 0, true)), indivIDs);
					}
					done = true;
				} catch (ClassCastException ex) {
					throw new RendererException(ex.getMessage());
				}
			}
			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(enumClass, classID, dep, annos, indivIDs
							.reverse())), resList);
		}

		if (!done) {

			/* We need to give at least an empty definition */
			mod = strToATermAppl1("Partial");

			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(classFun, classID, dep, mod, annos, factory
							.makeList())), resList);
		}

		// return is an ATermAppl: ATermOfClass(classID, ClassAxiomList)
		// AFun classAFun = factory.makeAFun("ATermOfClass", 2, false);
		return resList;
	}

	public ATermAppl renderIndividual(OWLOntology ontology, OWLIndividual ind)
			throws OWLException {

		// Individual (Maybe IndividualID) [Annotation] [Type] [Value]
		AFun consFun = factory.makeAFun("Indiv", 1, false);
		AFun indivFun = factory.makeAFun("Individual", 4, false);
		ATermAppl indivID = strToATermAppl("");
		ATermList annos = factory.makeList();
		ATermList types = factory.makeList();
		ATermList values = factory.makeList();
		AFun typeFun = factory.makeAFun("Type", 1, false);
		AFun valueIDFun = factory.makeAFun("ValueID", 2, false);
		AFun valueDLFun = factory.makeAFun("ValueDL", 2, false);
		
		if (ind.isAnonymous()) {
			Map m = ind.getIncomingObjectPropertyValues(ontology);
			if (!m.isEmpty()) {
				indivID = strToATermAppl1("Nothing");
			} else {
				indivID = factory.makeAppl(justFun,
						strToATermAppl(shortForm(ind.getURI())));
			}
		} else {
			indivID = factory.makeAppl(justFun, strToATermAppl(shortForm(ind
					.getURI())));
		}
		// pw.print("Individual(" + shortForm(ind.getURI()));
		//	}
		if (ind.getAnnotations(ontology).isEmpty()
				&& ind.getTypes(ontology).isEmpty()
				&& ind.getObjectPropertyValues(ontology).keySet().isEmpty()
				&& ind.getDataPropertyValues(ontology).keySet().isEmpty()) {
			// pw.print(")");

			return factory.makeAppl(fcFun, factory.makeAppl(consFun, factory.makeAppl(indivFun, indivID, emptyList, emptyList,
					emptyList)));
		} else {

			annos = makeAnno(ind.getAnnotations(ontology).iterator());

			for (Iterator it = ind.getTypes(ontology).iterator(); it.hasNext();) {
				OWLDescription eq = (OWLDescription) it.next();

				visitor.reset();
				eq.accept(visitor);

				ATerm resType = mkOther(visitor.result());
				//ATermAppl resType = factory.makeAppl(typeFun, mkOther(visitor
				//		.result()));
				types = factory.makeList(resType, types);
			}

			// recusive function call for "value IndividualvaluePropertyID
			// Individual" can result in deadlock.
			// here is only "value IndivudualvaluePropertyID IndividualID" used.
			Map propertyValues = ind.getObjectPropertyValues(ontology);
			for (Iterator it = propertyValues.keySet().iterator(); it.hasNext();) {
				OWLObjectProperty prop = (OWLObjectProperty) it.next();
				Iterator valIt = ((Set) propertyValues.get(prop)).iterator();

				for (; valIt.hasNext();) {

					OWLIndividual oi = (OWLIndividual) valIt.next();
					//					visitor.reset();
					//					oi.accept(visitor);
					//					ATermAppl resValue = factory.makeAppl(valueFun, propURI,
					// strToATermAppl(mkOther(visitor.result())));

					ATermAppl propURI = strToATermAppl(shortForm(prop.getURI()));
					// 					ATermAppl resValue = factory.makeAppl(valueIndivFun,
					// propURI, renderIndividual(ontology,oi));

					// AFun ivf = factory.makeAFun("IndividualID", 1, false);
					// ATermAppl iv = factory.makeAppl(ivf,
					// 		strToATermAppl(shortForm(oi.getURI())));
					ATermAppl resValue = factory.makeAppl(valueIDFun, propURI,
							strToATermAppl(shortForm(oi.getURI())));
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
					ATermAppl resValue = factory.makeAppl(valueDLFun, propURI,
							mkOther(visitor.result()));
					values = factory.makeList(resValue, values);
					// pw.print(", value(" + shortForm(prop.getURI()) + ", "
					//		+ mkOther(visitor.result()) + ")");
				}
			}
			return factory.makeAppl(fcFun, factory.makeAppl(consFun, factory.makeAppl(indivFun, indivID, annos, types, values)));
		}
	}

	public ATermAppl renderAnnotationProperty(OWLOntology ontology,
			OWLAnnotationProperty prop) throws OWLException {

		// Writer writer = new StringWriter();
		// setWriter(writer);

		AFun apFun = factory.makeAFun("AnnotationProperty", 2, false);
		Set apSet = prop.getAnnotations();
		Iterator it = apSet.iterator();
		// Iterator it = OntologyHelper.getAnnotations(ontology, ontology
		// ,prop).iterator();

		ATermList annoList = makeAnno(it);
		ATermAppl uri = strToATermAppl(shortForm(prop.getURI()));
		// pw.print("AnnotationProperty(" + shortForm(prop.getURI()) + ")");
		return factory.makeAppl(axFun, factory.makeAppl(apFun, uri, annoList));
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

		ATermAppl function = strToATermAppl1("Nothing");
		ATermAppl symmetric = strToATermAppl("");
		// AFun inverseOfFun = factory.makeAFun("InverseOf", 1, false);
		ATermAppl inverseOf = strToATermAppl1("Nothing");
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
		deprecated = prop.isDeprecated(ontology) ? strToATermAppl1("true")
				: strToATermAppl1("false");

		// function
		if(prop.isInverseFunctional(ontology) && prop.isFunctional(ontology)){
			function = factory.makeAppl(justFun, strToATermAppl1("Functional_InverseFunctional"));
		} else
		if (prop.isTransitive(ontology)) {
			function = factory.makeAppl(justFun, strToATermAppl1("Transitive"));
			// pw.print(", Transitive");
		} else
		if (prop.isFunctional(ontology)) {
			function = factory.makeAppl(justFun, strToATermAppl1("Functional"));
			// pw.print(", Functional");
		} else
		if (prop.isInverseFunctional(ontology)) {
			function = factory.makeAppl(justFun, strToATermAppl1("InverseFunctional"));
			// pw.print(", InverseFunctional");
		}
//		if (prop.isSymmetric(ontology)) {
		symmetric = prop.isSymmetric(ontology)? strToATermAppl1("true"): strToATermAppl1("false");
			// pw.print(", Symmetric");
//		}

		// only one inverseOf of ObjectProperty (see AS)
		for (Iterator it = prop.getInverses(ontology).iterator(); it.hasNext();) {

			OWLObjectProperty inv = (OWLObjectProperty) it.next();
			visitor.reset();
			inv.accept(visitor);

			inverseOf = factory.makeAppl(justFun, mkOther(visitor.result()));
			// pw.print(", inverseOf(" + mkOther(visitor.result()) + ")");
		}

		// a List of super property

		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {

			OWLObjectProperty sup = (OWLObjectProperty) it.next();
			visitor.reset();
			sup.accept(visitor);

			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			superList = factory.makeList(result, superList);

			// pw.print(", super(" + mkOther(visitor.result()) + ")");
		}
		superList = superList.reverse();

		// a list of domain
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {

			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);

			ATermAppl result = (ATermAppl) mkOther(visitor.result());
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

			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			rangeList = factory.makeList(result, rangeList);
			// pw.print(", range(" + mkOther(visitor.result()) + ")");
		}
		rangeList = rangeList.reverse();

		// pw.print(")");
		// return writer.toString();
		ATerm[] aterms = { indivID, deprecated, annoList, superList, inverseOf,
				symmetric, function, domainList, rangeList };

		return factory.makeAppl(axFun, factory.makeAppl(opFun, aterms));
	}

	public ATermAppl renderDataProperty(OWLOntology ontology,
			OWLDataProperty prop) throws OWLException {

		//		Writer writer = new StringWriter();
		//		setWriter(writer);
		//	DatatypeProperty DatavaluedPropertyID
		//                    Bool -- ^ True == deprecated
		//					  [Annotation]
		//					  [DatavaluedPropertyID] -- ^ super properties
		//					  (Maybe Func)
		//					  [Description] -- ^ Domain
		//				      [DataRange] -- ^ Range
		AFun dtpFun = factory.makeAFun("DatatypeProperty", 7, false);
		ATermAppl dvpID = strToATermAppl(shortForm(prop.getURI()));
		ATermList annoList = emptyList;
		ATermAppl deprecated = strToATermAppl1("false");
		ATermAppl functional = strToATermAppl1("false");
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
			deprecated = strToATermAppl1("true");
		}
		// maybe functional
		if (prop.isFunctional(ontology)) {
			//pw.print(", Functional");
			functional = strToATermAppl1("true");
		}

		// a List of super property
		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {

			OWLObjectProperty sup = (OWLObjectProperty) it.next();
			visitor.reset();
			sup.accept(visitor);

			ATermAppl result = factory.makeAppl(superFun, mkOther(visitor
					.result()));
			superList = factory.makeList(result, superList);

			// pw.print(", super(" + mkOther(visitor.result()) + ")");
		}
		superList = superList.reverse();

		// a list of domain
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {

			OWLDescription dom = (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);

			ATermAppl result = (ATermAppl) mkOther(visitor.result());
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

			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			rangeList = factory.makeList(result, rangeList);
			// pw.print(", range(" + mkOther(visitor.result()) + ")");
		}
		rangeList = rangeList.reverse();

		/*
		 * for (Iterator it = prop.getDomains(ontology).iterator();
		 * it.hasNext();) {
		 * 
		 * OWLDescription dom = (OWLDescription) it.next(); visitor.reset();
		 * dom.accept(visitor); pw.print(", domain(" + mkOther(visitor.result()) +
		 * ")"); // if (it.hasNext()) { // pw.print(); // } } for (Iterator it =
		 * prop.getRanges(ontology).iterator(); it.hasNext();) {
		 * 
		 * OWLDataRange ran = (OWLDa