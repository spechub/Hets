//import java.net.URI;

import java.util.HashSet;
import java.util.Iterator;
//import java.util.Map;
import java.util.Set;

//import org.mindswap.pellet.EconnectedKB;
import org.mindswap.pellet.KnowledgeBase;
//import org.mindswap.pellet.Role;
//import org.mindswap.pellet.utils.ATermUtils;
import org.mindswap.pellet.utils.URIUtils;
//import org.semanticweb.owl.impl.model.OWLConnectionImpl;
//import org.semanticweb.owl.io.owl_rdf.OWLRDFParser;
import org.semanticweb.owl.io.vocabulary.OWLVocabularyAdapter;
import org.semanticweb.owl.io.vocabulary.RDFSVocabularyAdapter;
import org.semanticweb.owl.io.vocabulary.RDFVocabularyAdapter;
//import org.semanticweb.owl.model.OWLClass;
//import org.semanticweb.owl.model.OWLClassAxiom;
//import org.semanticweb.owl.model.OWLDataProperty;
//import org.semanticweb.owl.model.OWLDataRange;
//import org.semanticweb.owl.model.OWLDataType;
//import org.semanticweb.owl.model.OWLDataValue;
//import org.semanticweb.owl.model.OWLDescription;
//import org.semanticweb.owl.model.OWLEnumeration;
//import org.semanticweb.owl.model.OWLException;
//import org.semanticweb.owl.model.OWLIndividual;
//import org.semanticweb.owl.model.OWLIndividualAxiom;
//import org.semanticweb.owl.model.OWLObject;
//import org.semanticweb.owl.model.OWLObjectProperty;
//import org.semanticweb.owl.model.OWLOntology;
//import org.semanticweb.owl.model.OWLPropertyAxiom;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLObject;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.helper.OntologyHelper;

import aterm.ATerm;
import aterm.ATermAppl;

public class OWL2ATermLoader {
	public static boolean DEBUG = false;

	private KnowledgeBase kb;

	private Set loadedFiles;

	private boolean loadImports = true;

	private Set ontologies;

	private OWL2ATermVisitor visitor;

	public OWL2ATermLoader(KnowledgeBase kb, OWLOntology onto) {
		this.kb = kb;
		this.visitor = new OWL2ATermVisitor(this, onto);
		reset();
	}

	/**
	 * @return Returns the useImports.
	 */
	public boolean loadImports() {
		return loadImports;
	}

	/**
	 * @param useImports
	 *            The useImports to set.
	 */
	public void setLoadImports(boolean loadImports) {
		this.loadImports = loadImports;
	}

	public void reset() {
		kb.clear();
		ontologies = new HashSet();
		loadedFiles = new HashSet();
		loadedFiles.add(URIUtils.getNameSpace(OWLVocabularyAdapter.OWL));
		loadedFiles.add(URIUtils.getNameSpace(RDFVocabularyAdapter.RDF));
		loadedFiles.add(URIUtils.getNameSpace(RDFSVocabularyAdapter.RDFS));
	}

	public ATermAppl getNamespace() {
		return visitor.getNamespace();
	}

	public void load(OWLOntology ontology) throws OWLException {
		if (loadImports) {
			Iterator i = OntologyHelper.importClosure(ontology).iterator();
			while (i.hasNext())
				loadOntology((OWLOntology) i.next());
		} else
			loadOntology(ontology);
	}

	public KnowledgeBase getKB() {
		return kb;
	}

	public void setKB(KnowledgeBase kb) {
		this.kb = kb;
	}

	public ATerm term(OWLObject d) throws OWLException {
		visitor.reset();
		d.accept(visitor);

		ATerm a = visitor.result();

		if (a == null)
			throw new OWLException("Cannot create ATerm from description " + d);

		return a;
	}

	void loadOntology(OWLOntology ontology) throws OWLException {

	}

	/**
	 * @return Returns the ontologies.
	 */
	public Set getOntologies() {
		return ontologies;
	}

}
