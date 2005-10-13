import aterm.*;
import aterm.pure.PureFactory;
import java.io.PrintStream;
import java.io.Writer;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.*;
import org.semanticweb.owl.io.*;
import org.semanticweb.owl.io.vocabulary.*;
import org.semanticweb.owl.model.*;
import org.semanticweb.owl.model.helper.OntologyHelper;

/**
 * Produces abstract syntax from OWL ontologies.
 * 
 * 
 * Created: Fri Feb 21 09:12:03 2003
 * 
 * @author Heng Jiang
 * @version $Id$
 */
public class ATermRender2 implements Renderer, ShortFormProvider {

	public ATermRender2(OWLOntology ontology) {
		emptyList = factory.makeList();
		axFun = factory.makeAFun("Ax", 1, false);
		fcFun = factory.makeAFun("Fc", 1, false);
		annoFun = factory.makeAFun("Anno", 1, false);
		superFun = factory.makeAFun("Super", 1, false);
		justFun = factory.makeAFun("Just", 1, false);
		visitor = new RenderingVisitor2(this, ontology);
		try {
			allURIs = OntologyHelper.allURIs(ontology);
		} catch (Exception e) {
			System.out.println((new StringBuilder(
					"Exception by constructor: ATermRender2:\n")).append(e)
					.toString());
		}
	}

	public void setOptions(Map map1) {
	}

	public Map getOptions() {
		return null;
	}

	public void renderOntology(OWLOntology owlontology, Writer writer1)
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
			dep = strToATermAppl1(clazz.isDeprecated(ontology) ? "true"
					: "false");
		}
		if (!clazz.getAnnotations(ontology).isEmpty())
			annos = makeAnno(clazz.getAnnotations().iterator());
		if (!clazz.getEquivalentClasses(ontology).isEmpty()) {
			mod = strToATermAppl1("Complete");
			for (Iterator it = clazz.getEquivalentClasses(ontology).iterator(); it
					.hasNext();) {
				OWLDescription eq = (OWLDescription) (OWLDescription) it.next();
				visitor.reset();
				eq.accept(visitor);
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
				OWLDescription eq = (OWLDescription) (OWLDescription) it.next();
				visitor.reset();
				eq.accept(visitor);
				descs = factory.makeList(mkOther(visitor.result()), descs);
				done = true;
			}

			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(classFun, classID, dep, mod, annos, descs
							.reverse())), resList);
		}
		if (!clazz.getEnumerations(ontology).isEmpty()) {
			ATermList indivIDs = factory.makeList();
			AFun enumClass = factory.makeAFun("EnumeratedClass", 4, false);
			for (Iterator it = clazz.getEnumerations(ontology).iterator(); it
					.hasNext();) {
				OWLDescription eq = (OWLDescription) (OWLDescription) it.next();
				try {
					OWLEnumeration enumeration = (OWLEnumeration) eq;
					for (Iterator iit = enumeration.getIndividuals().iterator(); iit
							.hasNext();) {
						OWLIndividual ioe = (OWLIndividual) (OWLIndividual) iit
								.next();
						visitor.reset();
						ioe.accept(visitor);
						indivIDs = factory
								.makeList(factory.makeAppl(factory.makeAFun(
										visitor.result(), 0, true)), indivIDs);
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
			mod = strToATermAppl1("Partial");
			resList = factory.makeList(factory.makeAppl(axFun, factory
					.makeAppl(classFun, classID, dep, mod, annos, factory
							.makeList())), resList);
		}
		return resList;
	}

	public ATermAppl renderIndividual2(OWLOntology ontology, OWLIndividual ind)
			throws OWLException {

		AFun indivFun = factory.makeAFun("Individual", 4, false);
		ATermAppl indivID = strToATermAppl("");
		ATermList annos = factory.makeList();
		ATermList types = factory.makeList();
		ATermList values = factory.makeList();
		// AFun typeFun = factory.makeAFun("Type", 1, false);
		AFun valueIDFun = factory.makeAFun("ValueID", 2, false);
		AFun valueDLFun = factory.makeAFun("ValueDL", 2, false);
		AFun valuedIndivFun = factory.makeAFun("ValueIndiv", 2, false);
		if (ind.isAnonymous()) {
			Map m = ind.getIncomingObjectPropertyValues(ontology); // why not
																	// tests
																	// ind.getURI
																	// instead
																	// of
																	// getIncomingObjectPropertyValues?
			if (!m.isEmpty())
				indivID = strToATermAppl1("Nothing");
			else
				indivID = factory.makeAppl(justFun,
						strToATermAppl(shortForm(ind.getURI())));
		} else {
			indivID = factory.makeAppl(justFun, strToATermAppl(shortForm(ind
					.getURI())));
		}
		if (ind.getAnnotations(ontology).isEmpty()
				&& ind.getTypes(ontology).isEmpty()
				&& ind.getObjectPropertyValues(ontology).keySet().isEmpty()
				&& ind.getDataPropertyValues(ontology).keySet().isEmpty())
			return factory.makeAppl(indivFun,
					indivID, emptyList, emptyList, emptyList);
		annos = makeAnno(ind.getAnnotations(ontology).iterator());
		for (Iterator it = ind.getTypes(ontology).iterator(); it.hasNext();) {
			OWLDescription eq = (OWLDescription) (OWLDescription) it.next();
			visitor.reset();
			eq.accept(visitor);
			ATerm resType = mkOther(visitor.result());
			types = factory.makeList(resType, types);
		}

		Map propertyValues = ind.getObjectPropertyValues(ontology);
		for (Iterator it = propertyValues.keySet().iterator(); it.hasNext();) {
			OWLObjectProperty prop = (OWLObjectProperty) it.next();
			for (Iterator valIt = ((Set) propertyValues.get(prop)).iterator(); valIt
					.hasNext();) {
				OWLIndividual oi = (OWLIndividual) valIt.next();
				ATermAppl propURI = strToATermAppl(shortForm(prop.getURI()));
				ATermAppl resValue = null;
				if (oi.getURI() == null || oi.isAnonymous()) {
					resValue = factory.makeAppl(valuedIndivFun, propURI,
							renderIndividual2(ontology, oi));
				} else {
					resValue = factory.makeAppl(valueIDFun, propURI,
							strToATermAppl(shortForm(oi.getURI())));
				}
				values = factory.makeList(resValue, values);
			}

		}

		Map dataValues = ind.getDataPropertyValues(ontology);
		for (Iterator it = dataValues.keySet().iterator(); it.hasNext();) {
			OWLDataProperty prop = (OWLDataProperty) it.next();
			Set vals = (Set) (Set) dataValues.get(prop);
			for (Iterator valIt = vals.iterator(); valIt.hasNext();) {
				OWLDataValue dtv = (OWLDataValue) valIt.next();
				visitor.reset();
				dtv.accept(visitor);
				ATermAppl propURI = strToATermAppl(shortForm(prop.getURI()));
				ATermAppl resValue = factory.makeAppl(valueDLFun, propURI,
						mkOther(visitor.result()));
				values = factory.makeList(resValue, values);
			}

		}
		return factory.makeAppl(indivFun, indivID,
				annos, types, values);
	}

	public ATermAppl renderIndividual(OWLOntology ontology, OWLIndividual ind)
			throws OWLException {
		AFun consFun = factory.makeAFun("Indiv", 1, false);
		return factory.makeAppl(fcFun, factory.makeAppl(consFun,  renderIndividual2(ontology, ind)));
	}

	public ATermAppl renderAnnotationProperty(OWLOntology ontology,
			OWLAnnotationProperty prop) throws OWLException {
		AFun apFun = factory.makeAFun("AnnotationProperty", 2, false);
		Set apSet = prop.getAnnotations();
		Iterator it = apSet.iterator();
		ATermList annoList = makeAnno(it);
		ATermAppl uri = strToATermAppl(shortForm(prop.getURI()));
		return factory.makeAppl(axFun, factory.makeAppl(apFun, uri, annoList));
	}

	public ATermAppl renderObjectProperty(OWLOntology ontology,
			OWLObjectProperty prop) throws OWLException {
		AFun opFun = factory.makeAFun("ObjectProperty", 9, false);
		ATermAppl indivID = strToATermAppl(shortForm(prop.getURI()));
		ATermAppl function = strToATermAppl1("Nothing");
		ATermAppl symmetric = strToATermAppl("");
		ATermAppl inverseOf = strToATermAppl1("Nothing");
		ATermList superList = emptyList;
		ATermList domainList = emptyList;
		ATermList rangeList = emptyList;
		ATermList annoList = emptyList;
		annoList = makeAnno(prop.getAnnotations().iterator());
		ATermAppl deprecated = prop.isDeprecated(ontology) ? strToATermAppl1("true")
				: strToATermAppl1("false");
		if (prop.isInverseFunctional(ontology) && prop.isFunctional(ontology))
			function = factory.makeAppl(justFun,
					strToATermAppl1("Functional_InverseFunctional"));
		else if (prop.isTransitive(ontology))
			function = factory.makeAppl(justFun, strToATermAppl1("Transitive"));
		else if (prop.isFunctional(ontology))
			function = factory.makeAppl(justFun, strToATermAppl1("Functional"));
		else if (prop.isInverseFunctional(ontology))
			function = factory.makeAppl(justFun,
					strToATermAppl1("InverseFunctional"));
		symmetric = prop.isSymmetric(ontology) ? strToATermAppl1("true")
				: strToATermAppl1("false");
		for (Iterator it = prop.getInverses(ontology).iterator(); it.hasNext();) {
			OWLObjectProperty inv = (OWLObjectProperty) (OWLObjectProperty) it
					.next();
			visitor.reset();
			inv.accept(visitor);
			inverseOf = factory.makeAppl(justFun, mkOther(visitor.result()));
		}

		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {
			OWLObjectProperty sup = (OWLObjectProperty) (OWLObjectProperty) it
					.next();
			visitor.reset();
			sup.accept(visitor);
			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			superList = factory.makeList(result, superList);
		}

		superList = superList.reverse();
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {
			OWLDescription dom = (OWLDescription) (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);
			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			domainList = factory.makeList(result, domainList);
		}

		domainList = domainList.reverse();
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {
			OWLDescription ran = (OWLDescription) (OWLDescription) it.next();
			visitor.reset();
			ran.accept(visitor);
			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			rangeList = factory.makeList(result, rangeList);
		}

		rangeList = rangeList.reverse();
		ATerm aterms[] = { indivID, deprecated, annoList, superList, inverseOf,
				symmetric, function, domainList, rangeList };
		return factory.makeAppl(axFun, factory.makeAppl(opFun, aterms));
	}

	public ATermAppl renderDataProperty(OWLOntology ontology,
			OWLDataProperty prop) throws OWLException {
		AFun dtpFun = factory.makeAFun("DatatypeProperty", 7, false);
		ATermAppl dvpID = strToATermAppl(shortForm(prop.getURI()));
		ATermList annoList = emptyList;
		ATermAppl deprecated = strToATermAppl1("false");
		ATermAppl functional = strToATermAppl1("false");
		ATermList superList = emptyList;
		ATermList domainList = emptyList;
		ATermList rangeList = emptyList;
		for (Iterator it = prop.getAnnotations().iterator(); it.hasNext();)
			annoList = makeAnno(it);

		if (prop.isDeprecated(ontology))
			deprecated = strToATermAppl1("true");
		if (prop.isFunctional(ontology))
			functional = strToATermAppl1("true");
		for (Iterator it = prop.getSuperProperties(ontology).iterator(); it
				.hasNext();) {
			OWLObjectProperty sup = (OWLObjectProperty) (OWLObjectProperty) it
					.next();
			visitor.reset();
			sup.accept(visitor);
			ATermAppl result = factory.makeAppl(superFun, mkOther(visitor
					.result()));
			superList = factory.makeList(result, superList);
		}

		superList = superList.reverse();
		for (Iterator it = prop.getDomains(ontology).iterator(); it.hasNext();) {
			OWLDescription dom = (OWLDescription) (OWLDescription) it.next();
			visitor.reset();
			dom.accept(visitor);
			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			domainList = factory.makeList(result, domainList);
		}

		domainList = domainList.reverse();
		for (Iterator it = prop.getRanges(ontology).iterator(); it.hasNext();) {
			OWLDataRange ran = (OWLDataRange) (OWLDataRange) it.next();
			visitor.reset();
			ran.accept(visitor);
			ATermAppl result = (ATermAppl) mkOther(visitor.result());
			rangeList = factory.makeList(result, rangeList);
		}

		rangeList = rangeList.reverse();
		return factory.makeAppl(axFun, factory.makeAppl(dtpFun, dvpID,
				deprecated, annoList, superList, functional, domainList,
				rangeList));
	}

	public ATermAppl renderDataType(OWLOntology ontology, OWLDataType datatype)
			throws OWLException {
		AFun dataTypeFun = factory.makeAFun("DataType", 3, false);
		ATermAppl isdep = datatype.isDeprecated(ontology) ? strToATermAppl1("true")
				: strToATermAppl1("false");
		ATermList annos = makeAnno(datatype.getAnnotations(ontology).iterator());
		ATermAppl result = factory.makeAppl(dataTypeFun,
				strToATermAppl(shortForm(datatype.getURI())), isdep, annos);
		return factory.makeAppl(axFun, result);
	}

	public ATermAppl renderClassAxiom(OWLClassAxiom axiom) throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		if (visitor.result() == null)
			return strToATermAppl("");
		else
			return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderPropertyAxiom(OWLPropertyAxiom axiom)
			throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		if (visitor.result() == null)
			return strToATermAppl("");
		else
			return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderIndividualAxiom(OWLIndividualAxiom axiom)
			throws OWLException {
		visitor.reset();
		axiom.accept(visitor);
		return (ATermAppl) mkOther(visitor.result());
	}

	public ATermAppl renderAnnotationInstance(OWLOntology ontology,
			OWLAnnotationInstance instance) throws OWLException {
		URI aiID = instance.getProperty().getURI();
		return renderAnnotationContent(true, instance.getContent(), aiID
				.toString());
	}

	public ATermAppl renderAnnotationContent(boolean isOntologyAnnotation,
			Object o, String annoID) throws OWLException {
		ATermAppl aid = strToATermAppl(annoID);
		if (isOntologyAnnotation && !annoID.contains("comment")
				&& !annoID.contains("label")) {
			AFun defaltFun = factory.makeAFun("OntoAnnotation", 2, false);
			return factory.makeAppl(annoFun, factory.makeAppl(defaltFun, aid,
					strToATermAppl(o.toString())));
		}
		if (o instanceof URI) {
			AFun uriAnnoFun = factory.makeAFun("URIAnnotation", 2, false);
			ATerm uriA = strToATermAppl(o.toString());
			return factory.makeAppl(uriAnnoFun, aid, uriA);
		}
		if (o instanceof OWLIndividual) {
			AFun indivFun = factory.makeAFun("IndivAnnotation", 2, false);
			ATerm indivA = strToATermAppl(((OWLIndividual) o).getURI()
					.toString());
			return factory.makeAppl(indivFun, aid, indivA);
		}
		if (o instanceof OWLDataValue) {
			AFun dlFun = factory.makeAFun("DLAnnotation", 2, false);
			AFun tlFun = factory.makeAFun("TypedL", 1, false);
			AFun plFun = factory.makeAFun("PlainL", 1, false);
			AFun literalFun = factory.makeAFun("", 2, false);
			OWLDataValue dv = (OWLDataValue) o;
			ATermAppl data = strToATermAppl(escape(dv.getValue()));
			ATermAppl result = strToATermAppl("");
			URI dvdt = dv.getURI();
			String dvlang = dv.getLang();
			if (dvdt != null) {
				ATermAppl uri = strToATermAppl(shortForm(dvdt));
				result = factory.makeAppl(tlFun, factory.makeAppl(literalFun,
						data, uri));
			} else if (dvlang != null) {
				ATermAppl tag = strToATermAppl(dvlang);
				result = factory.makeAppl(plFun, factory.makeAppl(literalFun,
						data, tag));
			} else {
				result = factory.makeAppl(plFun, factory.makeAppl(literalFun,
						data, strToATermAppl("")));
			}
			if (isOntologyAnnotation)
				return factory.makeAppl(annoFun, factory.makeAppl(dlFun, aid,
						result));
			else
				return factory.makeAppl(dlFun, aid, result);
		} else {
			return null;
		}
	}

	public static String escape(Object o) {
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
		shortNames = new ArrayList();
		known = new HashMap();
		OWLVocabularyAdapter _tmp = OWLVocabularyAdapter.INSTANCE;
		known.put("http://www.w3.org/2002/07/owl#", "owl");
		RDFVocabularyAdapter _tmp1 = RDFVocabularyAdapter.INSTANCE;
		known.put("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf");
		RDFSVocabularyAdapter _tmp2 = RDFSVocabularyAdapter.INSTANCE;
		known.put("http://www.w3.org/2000/01/rdf-schema#", "rdfs");
		XMLSchemaSimpleDatatypeVocabulary _tmp3 = XMLSchemaSimpleDatatypeVocabulary.INSTANCE;
		known.put("http://www.w3.org/2001/XMLSchema#", "xsd");
		for (Iterator it = allURIs.iterator(); it.hasNext();)
			try {
				URI uri = (URI) (URI) it.next();
				if (uri.getFragment() != null) {
					String ssp = (new URI(uri.getScheme(), uri
							.getSchemeSpecificPart(), null)).toString();
					if (!ssp.endsWith("#"))
						ssp = (new StringBuilder(String.valueOf(ssp))).append(
								"#").toString();
					if (!known.keySet().contains(ssp)
							&& !shortNames.contains(ssp))
						shortNames.add(ssp);
				}
			} catch (URISyntaxException urisyntaxexception) {
			}

	}

	public ATermAppl buildNamespaces() {
		AFun nsFun1 = factory.makeAFun("Namespace", 1, false);
		AFun nsFun2 = factory.makeAFun("NS", 2, false);
		ATermList nsList = emptyList;
		for (Iterator it = known.keySet().iterator(); it.hasNext();) {
			String ns = (String) (String) it.next();
			ATermAppl nsA = strToATermAppl(ns);
			ATermAppl shrt = strToATermAppl((String) (String) known.get(ns));
			nsList = factory.makeList(factory.makeAppl(nsFun2, shrt, nsA),
					nsList);
		}

		for (int i = 0; i < shortNames.size(); i++)
			if (i < names.length) {
				ATermAppl ns = strToATermAppl((String) (String) shortNames
						.get(i));
				ATermAppl nl = strToATermAppl(names[i]);
				nsList = factory.makeList(factory.makeAppl(nsFun2, nl, ns),
						nsList);
			}

		return factory.makeAppl(nsFun1, nsList.reverse());
	}

	public String shortForm(URI uri) {
		if (uri == null)
			return "_";
		try {
			if (uri.getFragment() == null || uri.getFragment().equals(""))
				return uri.toString();
			String ssp = (new URI(uri.getScheme(), uri.getSchemeSpecificPart(),
					null)).toString();
			if (!ssp.endsWith("#"))
				ssp = (new StringBuilder(String.valueOf(ssp))).append("#")
						.toString();
			if (known.keySet().contains(ssp))
				return (new StringBuilder(String
						.valueOf((String) (String) known.get(ssp))))
						.append(":").append(uri.getFragment()).toString();
			if (shortNames.contains(ssp)) {
				String frag = uri.getFragment();
				boolean fragOk = true;
				for (int i = 0; i < frag.length(); i++)
					fragOk = fragOk
							&& (Character.isLetter(frag.charAt(i))
									|| Character.isDigit(frag.charAt(i)) || frag
									.charAt(i) == '_');

				if (fragOk && shortNames.indexOf(ssp) < names.length)
					return (new StringBuilder(String.valueOf(names[shortNames
							.indexOf(ssp)]))).append(":").append(frag)
							.toString();
				else
					return uri.toString();
			}
		} catch (URISyntaxException ex) {
			System.out.println((new StringBuilder(
					"Exception by buiding an shortform of URI:")).append(ex)
					.toString());
		}
		return uri.toString();
	}

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
		if (term == null || "".equals(term))
			return strToATermAppl("_");
		String result = term;
		try {
			return factory.parse(result);
		} catch (Exception e) {
			return factory.parse((new StringBuilder("\"")).append(result)
					.append("\"").toString());
		}
	}

	private ATermList makeAnno(Iterator it) throws OWLException {
		ATermList annos = factory.makeList();
		OWLAnnotationInstance oai;
		for (; it.hasNext(); oai.accept(visitor)) {
			oai = (OWLAnnotationInstance) (OWLAnnotationInstance) it.next();
			ATermAppl annoCont = renderAnnotationContent(false, oai
					.getContent(), shortForm(oai.getProperty().getURI()));
			annos = factory.makeList(annoCont, annos);
			visitor.reset();
		}

		return annos.reverse();
	}

	public ATerm mkSimpleDescription(OWLDescription o) throws OWLException {
		visitor.reset();
		o.accept(visitor);
		return mkOther(visitor.result());
	}

	public ATerm mkSimpleIndividual(OWLIndividual o) throws OWLException {
		visitor.reset();
		o.accept(visitor);
		return mkOther(visitor.result());
	}

	public static ATermAppl strToATermAppl(String str) {
		return factory.makeAppl(factory.makeAFun(str, 0, true));
	}

	public static ATermAppl strToATermAppl1(String str) {
		return factory.makeAppl(factory.makeAFun(str, 0, false));
	}

	Set allURIs;

	List shortNames;

	Map known;

	int reservedNames;

	RenderingVisitor2 visitor;

	String names[] = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
			"l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x",
			"y", "z" };

	static PureFactory factory = new PureFactory();

	ATermList emptyList;

	AFun axFun;

	AFun fcFun;

	AFun annoFun;

	AFun superFun;

	AFun justFun;

}
