
import java.net.URI;
// import java.net.URISyntaxException;
// import java.util.ArrayList;
// import java.util.Comparator;
// import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
// import java.util.SortedSet;
// import java.util.TreeSet;

import org.mindswap.pellet.KnowledgeBase;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.utils.ATermUtils;
// import org.semanticweb.owl.io.abstract_syntax.RenderingVisitor;
// import org.semanticweb.owl.io.RendererException;
import org.semanticweb.owl.io.abstract_syntax.Renderer;
import org.semanticweb.owl.io.vocabulary.OWLVocabularyAdapter;
// import org.semanticweb.owl.io.vocabulary.RDFSVocabularyAdapter;
// import org.semanticweb.owl.io.vocabulary.RDFVocabularyAdapter;
// import org.semanticweb.owl.io.vocabulary.XMLSchemaSimpleDatatypeVocabulary;
import org.semanticweb.owl.model.OWLAnd;
import org.semanticweb.owl.model.OWLAnnotationInstance;
import org.semanticweb.owl.model.OWLAnnotationProperty;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.model.OWLDataAllRestriction;
import org.semanticweb.owl.model.OWLDataCardinalityRestriction;
import org.semanticweb.owl.model.OWLDataEnumeration;
import org.semanticweb.owl.model.OWLDataProperty;
import org.semanticweb.owl.model.OWLDataSomeRestriction;
import org.semanticweb.owl.model.OWLDataType;
import org.semanticweb.owl.model.OWLDataValue;
import org.semanticweb.owl.model.OWLDataValueRestriction;
import org.semanticweb.owl.model.OWLDescription;
import org.semanticweb.owl.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owl.model.OWLDisjointClassesAxiom;
// import org.semanticweb.owl.model.OWLEntity;
import org.semanticweb.owl.model.OWLEnumeration;
import org.semanticweb.owl.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owl.model.OWLEquivalentPropertiesAxiom;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLFrame;
import org.semanticweb.owl.model.OWLIndividual;
import org.semanticweb.owl.model.OWLIndividualAxiom;
import org.semanticweb.owl.model.OWLNamedObject;
import org.semanticweb.owl.model.OWLNot;
import org.semanticweb.owl.model.OWLObjectAllRestriction;
import org.semanticweb.owl.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owl.model.OWLObjectProperty;
import org.semanticweb.owl.model.OWLObjectSomeRestriction;
import org.semanticweb.owl.model.OWLObjectValueRestriction;
import org.semanticweb.owl.model.OWLObjectVisitor;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLOr;
import org.semanticweb.owl.model.OWLProperty;
import org.semanticweb.owl.model.OWLSameIndividualsAxiom;
import org.semanticweb.owl.model.OWLSubClassAxiom;
import org.semanticweb.owl.model.OWLSubPropertyAxiom;
import org.semanticweb.owl.model.helper.OntologyHelper;

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;

import java.util.Map;

/**
 * PelletVisitor
 *  
 */

public class OWL2ATermVisitor implements OWLObjectVisitor {
	/**
	 * Comment for <code>serialVersionUID</code>
	 */
	private static final long serialVersionUID = 1L;

	public static boolean DEBUG = false;

	private static OWLVocabularyAdapter OWL = OWLVocabularyAdapter.INSTANCE;

	OWL2ATermLoader loader;

	OWLOntology ontology;

	ATerm term;

	ATermAppl namespaces;

	private Set allURIs;

	private List shortNames;

	private Map known;

	private int reservedNames;

	private ATermRender2 visitRend;

	/*
	 * private String[] names = { "a", "b", "c", "d", "e", "f", "g", "h", "i",
	 * "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w",
	 * "x", "y", "z", };
	 */
	public OWL2ATermVisitor(OWL2ATermLoader loader, OWLOntology onto) {
		this.loader = loader;
		this.ontology = onto;
		try {
			this.allURIs = OntologyHelper.allURIs(ontology);
		} catch (Exception e) {
			System.out.println("Constructor of OWL2ATermVisitor: " + e);
		}
		visitRend = new ATermRender2(ontology);
		visitRend.generateShortNames();
		namespaces = visitRend.buildNamespaces();
	}

	public ATerm result() {
		return term;
	}

	public void reset() {
		term = null;
	}

	public ATermAppl getNamespace() {
		return namespaces;
	}

	
//
//    public void visit( OWLDataValue cd ) throws OWLException {
//    	
//    	
//    	pw.print( "\"" + Renderer.escape( cd.getValue() ) + "\"");
//
//    	/* Only show it if it's not string */
//
//    	URI dvdt = cd.getURI();
//    	String dvlang = cd.getLang();
//    	if ( dvdt!=null) {
//    	    pw.print( "^^" + "<" + dvdt.toString() + ">");
//    	} else {
//    	    if (dvlang!=null) {
//    		pw.print( "@" + dvlang );
//    	    }
//    	}	
//    }
	
	public ATermAppl term(OWLDataValue dv) throws OWLException {
		URI datatypeURI = dv.getURI();
		String lexicalValue = dv.getValue().toString();
		String lang = dv.getLang();

		if (datatypeURI != null)
			return ATermUtils.makeTypedLiteral(lexicalValue, datatypeURI
					.toString());
		else if (lang != null)
			return ATermUtils.makePlainLiteral(lexicalValue, lang);
		else
			return ATermUtils.makePlainLiteral(lexicalValue);
	}

	public ATermAppl term(OWLNamedObject o) throws OWLException {
		URI uri = o.getURI();
		if (uri == null) {
			if (o instanceof OWLIndividual) {
				return term("anon-" + o.hashCode());
			}
			throw new OWLException("No name can be created for " + o);
		} else
			return term(uri);
	}

	public ATermAppl term(String s) {
		return ATermUtils.makeTermAppl(s);
	}

	public ATermAppl term(URI u) {
		if (u.toString().equals(OWL.getThing()))
			return ATermUtils.TOP;
		if (u.toString().equals(OWL.getNothing()))
			return ATermUtils.BOTTOM;
		if (PelletOptions.USE_LOCAL_NAME)
			return term(u.getFragment());

		return term(u.toString());
	}

	public void visit(OWLClass clazz) throws OWLException {
		term = visitRend.renderClass(ontology, clazz);
	}

	public void visit(OWLIndividual ind) throws OWLException {
		term = visitRend.renderIndividual(ontology, ind);
	}

	public void visit(OWLIndividualAxiom axiom) throws OWLException {
		// System.out.println("YOHO! in AV " );
		term = visitRend.renderIndividualAxiom(axiom);
	}

	public void visit(OWLObjectProperty prop) throws OWLException {
		term = visitRend.renderObjectProperty(ontology, prop);
	}

	public void visit(OWLDataProperty prop) throws OWLException {
		term = visitRend.renderDataProperty(ontology, prop);
	}

	
	public void visit(OWLDataValue cd) throws OWLException {
		term = term(cd);
	}
	
	public void visit(OWLDataType ocdt) throws OWLException {
		term = visitRend.renderDataType(ontology, ocdt);
	}

	public void visit(OWLAnd and) throws OWLException {
		ATermList ops = ATermUtils.makeList();
		for (Iterator it = and.getOperands().iterator(); it.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			ops = ops.insert(result());
		}
		// term = term(visitRend.renderClassAxiom(and.));

		term = ATermUtils.makeAnd(ops);
	}

	public void visit(OWLOr or) throws OWLException {
		ATermList ops = ATermUtils.makeList();
		for (Iterator it = or.getOperands().iterator(); it.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			ops = ops.insert(result());
		}
		term = ATermUtils.makeOr(ops);
	}

	public void visit(OWLNot not) throws OWLException {
		OWLDescription desc = not.getOperand();
		desc.accept(this);

		term = ATermUtils.makeNot(term);
	}

	public void visit(OWLEnumeration enumeration) throws OWLException {
		ATermList ops = ATermUtils.makeList();
		for (Iterator it = enumeration.getIndividuals().iterator(); it
				.hasNext();) {
			OWLIndividual desc = (OWLIndividual) it.next();
			desc.accept(this);
			ops = ops.insert(ATermUtils.makeValue(result()));
		}
		term = ATermUtils.makeOr(ops);
	}

	public void visit(OWLObjectSomeRestriction restriction) throws OWLException {
		restriction.getObjectProperty().accept(this);
		ATerm p = term;
		restriction.getDescription().accept(this);
		ATerm c = term;

		term = ATermUtils.makeSomeValues(p, c);
	}

	public void visit(OWLObjectAllRestriction restriction) throws OWLException {
		restriction.getObjectProperty().accept(this);
		ATerm p = term;
		restriction.getDescription().accept(this);
		ATerm c = term;

		term = ATermUtils.makeAllValues(p, c);
	}

	public void visit(OWLObjectValueRestriction restriction)
			throws OWLException {
		restriction.getObjectProperty().accept(this);
		ATerm p = term;
		restriction.getIndividual().accept(this);
		ATerm ind = term;

		term = ATermUtils.makeSomeValues(p, ATermUtils.makeValue(ind));
	}

	public void visit(OWLObjectCardinalityRestriction restriction)
			throws OWLException {
		if (restriction.isExactly()) {
			restriction.getObjectProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtLeast();

			term = ATermUtils.makeCard(p, n);

		} else if (restriction.isAtMost()) {
			restriction.getObjectProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtMost();

			term = ATermUtils.makeMax(p, n);

		} else if (restriction.isAtLeast()) {
			restriction.getObjectProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtLeast();

			term = ATermUtils.makeMin(p, n);
		}
	}

	public void visit(OWLDataCardinalityRestriction restriction)
			throws OWLException {
		if (restriction.isExactly()) {
			restriction.getDataProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtLeast();

			term = ATermUtils.makeCard(p, n);

		} else if (restriction.isAtMost()) {
			restriction.getDataProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtMost();

			term = ATermUtils.makeMax(p, n);

		} else if (restriction.isAtLeast()) {
			restriction.getDataProperty().accept(this);
			ATerm p = term;
			int n = restriction.getAtLeast();

			term = ATermUtils.makeMin(p, n);
		}
	}

	public void visit(OWLEquivalentClassesAxiom axiom) throws OWLException {
		KnowledgeBase kb = loader.getKB();

		Iterator eqs = axiom.getEquivalentClasses().iterator();
		if (eqs.hasNext()) {
			OWLDescription desc1 = (OWLDescription) eqs.next();
			desc1.accept(this);
			ATerm c1 = term;

			while (eqs.hasNext()) {
				OWLDescription desc2 = (OWLDescription) eqs.next();
				desc2.accept(this);
				ATerm c2 = term;

				//	kb.addSameClass(c1, c2);
			}
		}
	}

	public void visit(OWLDisjointClassesAxiom axiom) throws OWLException {
		KnowledgeBase kb = loader.getKB();

		Object[] disjs = axiom.getDisjointClasses().toArray();
		for (int i = 0; i < disjs.length; i++) {
			for (int j = i + 1; j < disjs.length; j++) {
				OWLDescription desc1 = (OWLDescription) disjs[i];
				OWLDescription desc2 = (OWLDescription) disjs[j];
				desc1.accept(this);
				ATerm c1 = term;
				desc2.accept(this);
				ATerm c2 = term;

				kb.addDisjointClass(c1, c2);
			}
		}
	}

	public void visit(OWLSubClassAxiom axiom) throws OWLException {
		axiom.getSubClass().accept(this);
		ATerm c1 = term;
		axiom.getSuperClass().accept(this);
		ATerm c2 = term;

		// KnowledgeBase kb = loader.getKB();
		//kb.addSubClass(c1, c2);
	}

	public void visit(OWLEquivalentPropertiesAxiom axiom) throws OWLException {
		// KnowledgeBase kb = loader.getKB();

		Object[] eqs = axiom.getProperties().toArray();
		for (int i = 0; i < eqs.length; i++) {
			for (int j = i + 1; j < eqs.length; j++) {
				OWLProperty prop1 = (OWLProperty) eqs[i];
				OWLProperty prop2 = (OWLProperty) eqs[j];
				prop1.accept(this);
				ATerm p1 = term;
				prop2.accept(this);
				ATerm p2 = term;

				//kb.addSameProperty(p1, p2);
			}
		}
	}

	public void visit(OWLSubPropertyAxiom axiom) throws OWLException {

		axiom.getSubProperty().accept(this);
		ATerm p1 = term;
		axiom.getSuperProperty().accept(this);
		ATerm p2 = term;

		//KnowledgeBase kb = loader.getKB();
		//kb.addSubProperty(p1, p2);
	}

	public void visit(OWLDifferentIndividualsAxiom axiom) throws OWLException {
		//	KnowledgeBase kb = loader.getKB();

		Object[] inds = axiom.getIndividuals().toArray();
		for (int i = 0; i < inds.length; i++) {
			for (int j = i + 1; j < inds.length; j++) {
				ATerm i1 = loader.term((OWLIndividual) inds[i]);
				ATerm i2 = loader.term((OWLIndividual) inds[j]);

				//			kb.addDifferent(i1, i2);
			}
		}
	}

	public void visit(OWLSameIndividualsAxiom axiom) throws OWLException {
		//	KnowledgeBase kb = loader.getKB();

		Iterator eqs = axiom.getIndividuals().iterator();
		if (eqs.hasNext()) {
			ATerm i1 = loader.term((OWLIndividual) eqs.next());

			while (eqs.hasNext()) {
				ATerm i2 = loader.term((OWLIndividual) eqs.next());

				//				kb.addSame(i1, i2);
			}
		}
	}

	public void visit(OWLAnnotationProperty ap) {
		// skip annotation properties?
		try{
			term = visitRend.renderAnnotationProperty(ontology, ap);
		}catch(Exception e){
			term = null;
		}
	}

	public void visit(OWLAnnotationInstance ai) throws OWLException {
		term = visitRend.renderAnnotationInstance(ontology, ai);
		
		// skip annotation instances
	}

	public void visit(OWLDataEnumeration enumeration) throws OWLException {
		ATermList ops = ATermUtils.makeList();
		for (Iterator it = enumeration.getValues().iterator(); it.hasNext();) {
			OWLDataValue value = (OWLDataValue) it.next();
			value.accept(this);
			ops = ops.insert(ATermUtils.makeValue(result()));
		}
		term = ATermUtils.makeOr(ops);
	}

	public void visit(OWLDataAllRestriction restriction) throws OWLException {
		restriction.getDataProperty().accept(this);
		ATerm p = term;
		restriction.getDataType().accept(this);
		ATerm c = term;

		term = ATermUtils.makeAllValues(p, c);
	}

	public void visit(OWLDataSomeRestriction restriction) throws OWLException {
		restriction.getDataProperty().accept(this);
		ATerm p = term;
		restriction.getDataType().accept(this);
		ATerm c = term;

		term = ATermUtils.makeSomeValues(p, c);
	}

	public void visit(OWLDataValueRestriction restriction) throws OWLException {
		restriction.getDataProperty().accept(this);
		ATerm p = term;
		restriction.getValue().accept(this);
		ATerm dv = term;

		term = ATermUtils.makeSomeValues(p, ATermUtils.makeValue(dv));
	}

	public void visit(OWLFrame f) {
		// skip OWLFrame
	}

	public void visit(OWLOntology o) {
		// skip ontology
	}
}
