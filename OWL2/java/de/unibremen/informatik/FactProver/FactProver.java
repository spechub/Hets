package de.unibremen.informatik.FactProver;

import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAnnotationAssertionAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLAnnotationPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyCharacteristicAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDatatypeDefinitionAxiom;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentDataPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNaryAxiom;
import org.semanticweb.owlapi.model.OWLNaryClassAxiom;
import org.semanticweb.owlapi.model.OWLNaryIndividualAxiom;
import org.semanticweb.owlapi.model.OWLNaryPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNegativeDataPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyCharacteristicAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLPropertyAxiom;
import org.semanticweb.owlapi.model.OWLPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubDataPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLUnaryPropertyAxiom;
import org.semanticweb.owlapi.model.SWRLRule;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.search.EntitySearcher;

import uk.ac.manchester.cs.factplusplus.FaCTPlusPlusException;
import uk.ac.manchester.cs.factplusplus.owlapiv3.FaCTPlusPlusReasoner;

public class FactProver {
	private IRI iri;
	private FaCTPlusPlusReasoner reasoner;
	private OWLAxiom goal;

	public FactProver(IRI iri)
		throws OWLOntologyCreationException, FaCTPlusPlusException
	{
		this.iri = iri;
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology ontology =
			manager.loadOntologyFromOntologyDocument(this.iri);
		this.reasoner = new FaCTPlusPlusReasoner(ontology, 
			new SimpleConfiguration(), BufferingMode.BUFFERING);
	}

	public void loadGoal(IRI giri) throws OWLOntologyCreationException {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(giri);
		Set<OWLAxiom> axioms = ontology.getAxioms();
		for (Iterator<OWLAxiom> i = axioms.iterator(); i.hasNext();) {
			OWLAxiom ax = i.next();
			if (ax instanceof OWLDeclarationAxiom)
				i.remove();
		}
		if (axioms.size() == 1) {
			Iterator<OWLAxiom> it = axioms.iterator();
			this.goal = it.next();
		} else {
			throw new OWLOntologyCreationException("Too many axioms for conjecture");
		}
	}

	public boolean prove() throws FaCTPlusPlusException {
		if (goal instanceof OWLObjectPropertyAssertionAxiom) {
			OWLObjectPropertyAssertionAxiom g =
				(OWLObjectPropertyAssertionAxiom) goal;
			OWLIndividual object = g.getObject();
			OWLIndividual subject = g.getSubject();
			OWLObjectPropertyExpression prop = g.getProperty();
			NodeSet<OWLNamedIndividual> ind = reasoner
				.getObjectPropertyValues(object.asOWLNamedIndividual(), prop);
			return ind.containsEntity(subject.asOWLNamedIndividual());
		}
		if (goal instanceof OWLClassAssertionAxiom) {
			OWLClassAssertionAxiom g = (OWLClassAssertionAxiom) goal;
			OWLClassExpression cls = g.getClassExpression();
			OWLIndividual indi = g.getIndividual();
			NodeSet<OWLClass> n =
				reasoner.getTypes(indi.asOWLNamedIndividual(), true);
			return n.containsEntity(cls.asOWLClass());
		}
		if (goal instanceof OWLDataPropertyAssertionAxiom) {
			OWLDataPropertyAssertionAxiom g =
				(OWLDataPropertyAssertionAxiom) goal;
			OWLDataProperty prop = g.getProperty().asOWLDataProperty();
			OWLLiteral obj = g.getObject();
			OWLIndividual sub = g.getSubject();
			Set<OWLLiteral> litset = reasoner
				.getDataPropertyValues(sub.asOWLNamedIndividual(), prop);
			return litset.contains(obj);
		}
		if (goal instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom g = (OWLEquivalentClassesAxiom) goal;
			OWLClassExpression[] cls = g.getClassExpressions()
				.toArray(new OWLClassExpression[g.getClassExpressions().size()]);
			boolean res = true;
			for (int i = 0; i < cls.length; i++ ) {
				for (int j = 0; j < cls.length; j++ ) {
					if (i != j) {
						Node<OWLClass> c =
							reasoner.getEquivalentClasses(cls[i]);
						res &= c.contains(cls[j].asOWLClass());
					}
				}
			}
			return res;
		}
		if (goal instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom g = (OWLSubClassOfAxiom) goal;
			OWLClassExpression sub = g.getSubClass();
			OWLClassExpression top = g.getSuperClass();
			NodeSet<OWLClass> c = reasoner.getSubClasses(top, true);
			return c.containsEntity(sub.asOWLClass());
		}
		if (goal instanceof OWLDataPropertyRangeAxiom) {
			throw new FaCTPlusPlusException("Fact++ cannot determine data ranges!");
		}
		if (goal instanceof OWLDataPropertyDomainAxiom) {
			OWLDataPropertyDomainAxiom g = (OWLDataPropertyDomainAxiom) goal;
			OWLDataProperty prop = g.getProperty().asOWLDataProperty();
			OWLClassExpression d = g.getDomain();
			boolean res = false;
			NodeSet<OWLClass> dom = reasoner.getDataPropertyDomains(prop, true);
			Iterator<Node<OWLClass>> it = dom.iterator();
			while (it.hasNext()) {
				Node<OWLClass> cur = it.next();
				Iterator<OWLClass> itt = cur.iterator();
				while (itt.hasNext()) {
					OWLClass c = itt.next();
					Node<OWLClass> cl = reasoner.getEquivalentClasses(c);
					if (cl.contains(d.asOWLClass()))
						res = true;
				}
			}
			return res;
		}
		if (goal instanceof OWLSubDataPropertyOfAxiom) {
			OWLSubDataPropertyOfAxiom g = (OWLSubDataPropertyOfAxiom) goal;
			OWLDataProperty sub = g.getSubProperty().asOWLDataProperty();
			OWLDataProperty sup = g.getSuperProperty().asOWLDataProperty();
			boolean res = false;
			NodeSet<OWLDataProperty> sups =
				reasoner.getSuperDataProperties(sub, true);
			Iterator<Node<OWLDataProperty>> it = sups.iterator();
			while (it.hasNext()) {
				Node<OWLDataProperty> cur = it.next();
				if (cur.contains(sup))
					res = true;
			}
			return res;
		}
		if (goal instanceof OWLAsymmetricObjectPropertyAxiom) {
			throw new FaCTPlusPlusException("Fact++ cannot determine antisymmetry!");
		}
		if (goal instanceof OWLAnnotationAssertionAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLAnnotationAssertionAxiom!");
		}
		if (goal instanceof OWLAnnotationAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLAnnotationAxiom!");
		}
		if (goal instanceof OWLAnnotationPropertyDomainAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLAnnotationPropertyDomainAxiom!");
		}
		if (goal instanceof OWLAnnotationPropertyRangeAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLAnnotationPropertyRangeAxiom!");
		}
		if (goal instanceof OWLClassAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLClassAxiom!");
		}
		if (goal instanceof OWLDataPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDataPropertyAxiom!");
		}
		if (goal instanceof OWLDataPropertyCharacteristicAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDataPropertyCharacteristicAxiom!");
		}
		if (goal instanceof OWLDatatypeDefinitionAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDatatypeDefinitionAxiom!");
		}
		if (goal instanceof OWLDeclarationAxiom) {
			return true;
		}
		if (goal instanceof OWLDifferentIndividualsAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDifferentIndividualsAxiom!");
		}
		if (goal instanceof OWLDisjointClassesAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDisjointClassesAxiom!");
		}
		if (goal instanceof OWLDisjointDataPropertiesAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDisjointDataPropertiesAxiom!");
		}
		if (goal instanceof OWLDisjointObjectPropertiesAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDisjointObjectPropertiesAxiom!");
		}
		if (goal instanceof OWLDisjointUnionAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLDisjointUnionAxiom!");
		}
		if (goal instanceof OWLIndividualAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLIndividualAxiom!");
		}
		if (goal instanceof OWLLogicalAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLLogicalAxiom!");
		}
		if (goal instanceof OWLNaryAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLNaryAxiom!");
		}
		if (goal instanceof OWLNaryClassAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLNaryClassAxiom!");
		}
		if (goal instanceof OWLNaryIndividualAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLNaryIndividualAxiom!");
		}
		if (goal instanceof OWLNaryPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLNaryPropertyAxiom!");
		}
		if (goal instanceof OWLObjectPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLObjectPropertyAxiom!");
		}
		if (goal instanceof OWLObjectPropertyCharacteristicAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLObjectPropertyCharacteristicAxiom!");
		}
		if (goal instanceof OWLPropertyAssertionAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLPropertyAssertionAxiom!");
		}
		if (goal instanceof OWLPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLPropertyAxiom!");
		}
		if (goal instanceof OWLPropertyDomainAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLPropertyDomainAxiom!");
		}
		if (goal instanceof OWLPropertyRangeAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLPropertyRangeAxiom!");
		}
		if (goal instanceof OWLSameIndividualAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLSameIndividualAxiom!");
		}
		if (goal instanceof OWLSubAnnotationPropertyOfAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLSubAnnotationPropertyOfAxiom!");
		}
		if (goal instanceof OWLSubPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLSubPropertyAxiom!");
		}
		if (goal instanceof OWLSubPropertyChainOfAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLSubPropertyChainOfAxiom!");
		}
		if (goal instanceof OWLUnaryPropertyAxiom) {
			throw new FaCTPlusPlusException("FaCT++ cannot process OWLUnaryPropertyAxiom!");
		}
		if (goal instanceof SWRLRule) {
			throw new FaCTPlusPlusException("FaCT++ cannot process SWRLRule!");
		}
		if (goal instanceof OWLEquivalentDataPropertiesAxiom) {
			OWLEquivalentDataPropertiesAxiom g =
				(OWLEquivalentDataPropertiesAxiom) goal;
			Set<OWLDataPropertyExpression> props = g.getProperties();
			TreeSet<OWLDataProperty> p = new TreeSet<OWLDataProperty>();
			Iterator<OWLDataPropertyExpression> it = props.iterator();
			p.clear();
			while (it.hasNext()) {
				p.add(it.next().asOWLDataProperty());
			}
			boolean res = true;
			Iterator<OWLDataProperty> itt = p.iterator();
			while (itt.hasNext()) {
				Node<OWLDataProperty> cur =
					reasoner.getEquivalentDataProperties(itt.next());
				Set<OWLDataProperty> scur = cur.getEntities();
				res &= scur.containsAll(props);
			}
			return res;
		}
		if (goal instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom g =
				(OWLEquivalentObjectPropertiesAxiom) goal;
			Set<OWLObjectPropertyExpression> props = g.getProperties();
			TreeSet<OWLObjectPropertyExpression> p =
				new TreeSet<OWLObjectPropertyExpression>();
			Iterator<OWLObjectPropertyExpression> it = props.iterator();
			p.clear();
			while (it.hasNext()) {
				p.add(it.next());
			}
			boolean res = true;
			Iterator<OWLObjectPropertyExpression> itt = p.iterator();
			while (itt.hasNext()) {
				Node<OWLObjectPropertyExpression> cur =
					reasoner.getEquivalentObjectProperties(itt.next());
				Set<OWLObjectPropertyExpression> scur = cur.getEntities();
				res &= scur.containsAll(props);
			}
			return res;
		}
		if (goal instanceof OWLFunctionalDataPropertyAxiom) {
			OWLFunctionalDataPropertyAxiom g =
				(OWLFunctionalDataPropertyAxiom) goal;
			OWLDataProperty prop = g.getProperty().asOWLDataProperty();
			return EntitySearcher.isFunctional(prop, reasoner.getRootOntology());
		}
		if (goal instanceof OWLFunctionalObjectPropertyAxiom) {
			OWLFunctionalObjectPropertyAxiom g =
				(OWLFunctionalObjectPropertyAxiom) goal;
			OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
			return EntitySearcher.isFunctional(prop, reasoner.getRootOntology());
		}
		if (goal instanceof OWLInverseFunctionalObjectPropertyAxiom) {
			OWLInverseFunctionalObjectPropertyAxiom g =
				(OWLInverseFunctionalObjectPropertyAxiom) goal;
			OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
			return EntitySearcher.isInverseFunctional(prop, reasoner.getRootOntology());
		}
		if (goal instanceof OWLInverseObjectPropertiesAxiom) {
			OWLInverseObjectPropertiesAxiom g =
				(OWLInverseObjectPropertiesAxiom) goal;
			OWLObjectPropertyExpression fst = g.getFirstProperty();
			OWLObjectPropertyExpression snd = g.getSecondProperty();
			Node<OWLObjectPropertyExpression> is =
				reasoner.getInverseObjectProperties(fst);
			boolean res = false;
			if (is.contains(snd)) {
				res = true;
			}
			return res;
		}
		if (goal instanceof OWLIrreflexiveObjectPropertyAxiom) {
			OWLIrreflexiveObjectPropertyAxiom g =
				(OWLIrreflexiveObjectPropertyAxiom) goal;
			return EntitySearcher.isIrreflexive(g.getProperty().asOWLObjectProperty(),
				reasoner.getRootOntology());
		}
		if (goal instanceof OWLNegativeDataPropertyAssertionAxiom) {
			OWLNegativeDataPropertyAssertionAxiom g =
				(OWLNegativeDataPropertyAssertionAxiom) goal;
			OWLIndividual sub = g.getSubject();
			OWLLiteral obj = g.getObject();
			OWLDataProperty p = g.getProperty().asOWLDataProperty();
			Set<OWLLiteral> slit =
				reasoner.getDataPropertyValues(sub.asOWLNamedIndividual(), p);
			return slit.contains(obj);
		}
		if (goal instanceof OWLNegativeObjectPropertyAssertionAxiom) {
			OWLNegativeObjectPropertyAssertionAxiom g =
				(OWLNegativeObjectPropertyAssertionAxiom) goal;
			OWLIndividual sub = g.getSubject();
			OWLIndividual obj = g.getObject();
			OWLObjectProperty p = g.getProperty().asOWLObjectProperty();
			NodeSet<OWLNamedIndividual> ind =
				reasoner.getObjectPropertyValues(obj.asOWLNamedIndividual(), p);
			return ind.containsEntity(sub.asOWLNamedIndividual());
		}
		if (goal instanceof OWLObjectPropertyAssertionAxiom) {
			OWLObjectPropertyAssertionAxiom g =
				(OWLObjectPropertyAssertionAxiom) goal;
			OWLIndividual sub = g.getSubject();
			OWLIndividual obj = g.getObject();
			OWLObjectProperty p = g.getProperty().asOWLObjectProperty();
			NodeSet<OWLNamedIndividual> ind =
				reasoner.getObjectPropertyValues(obj.asOWLNamedIndividual(), p);
			return ind.containsEntity(sub.asOWLNamedIndividual());
		}
		if (goal instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom g =
				(OWLObjectPropertyDomainAxiom) goal;
			OWLObjectPropertyExpression prop = g.getProperty();
			OWLClassExpression dom = g.getDomain();
			NodeSet<OWLClass> doms =
				reasoner.getObjectPropertyDomains(prop, true);
			boolean res = false;
			Iterator<Node<OWLClass>> it = doms.iterator();
			while (it.hasNext()) {
				Node<OWLClass> cur = it.next();
				if (cur.contains(dom.asOWLClass())) {
					res = true;
				}
			}
			return res;
		}
		if (goal instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom g = (OWLObjectPropertyRangeAxiom) goal;
			OWLObjectPropertyExpression prop = g.getProperty();
			OWLClass ran = g.getRange().asOWLClass();
			NodeSet<OWLClass> rns =
				reasoner.getObjectPropertyRanges(prop, true);
			return rns.containsEntity(ran);
		}
		if (goal instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom g = (OWLSubObjectPropertyOfAxiom) goal;
			OWLObjectPropertyExpression sub = g.getSubProperty();
			OWLObjectPropertyExpression sup = g.getSuperProperty();
			NodeSet<OWLObjectPropertyExpression> subs =
				reasoner.getSubObjectProperties(sup, true);
			boolean res = false;
			Iterator<Node<OWLObjectPropertyExpression>> it = subs.iterator();
			while (it.hasNext()) {
				Node<OWLObjectPropertyExpression> cur = it.next();
				if (cur.contains(sub)) {
					res = true;
				}
			}
			return res;
		}
		if (goal instanceof OWLReflexiveObjectPropertyAxiom) {
			OWLReflexiveObjectPropertyAxiom g =
				(OWLReflexiveObjectPropertyAxiom) goal;
			OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
			return EntitySearcher.isReflexive(prop, reasoner.getRootOntology());
		}
		if (goal instanceof OWLSymmetricObjectPropertyAxiom) {
			OWLSymmetricObjectPropertyAxiom g =
				(OWLSymmetricObjectPropertyAxiom) goal;
			OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
			return EntitySearcher.isSymmetric(prop, reasoner.getRootOntology());
		}
		if (goal instanceof OWLTransitiveObjectPropertyAxiom) {
			OWLTransitiveObjectPropertyAxiom g =
				(OWLTransitiveObjectPropertyAxiom) goal;
			OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
			return EntitySearcher.isTransitive(prop, reasoner.getRootOntology());
		}
		System.out.println(goal);
		throw new FaCTPlusPlusException("No reasoner found, sorry!");
	}
}
