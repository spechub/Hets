package de.unibremen.informatik.FactProver;

import uk.ac.manchester.cs.factplusplus.owlapiv3.*;
import uk.ac.manchester.cs.factplusplus.*;
import uk.ac.manchester.cs.factplusplus.FaCTPlusPlus;

import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.net.URI;
import java.util.*;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.Node;

public class FactProver 
{

	private IRI iri;
	private FaCTPlusPlusReasoner reasoner;
        private OWLAxiom goal;

	public FactProver(IRI iri) throws OWLOntologyCreationException,
                                          FaCTPlusPlusException
	{
		this.iri = iri;
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
//		FaCTPlusPlusReasonerFactory fac = new FaCTPlusPlusReasonerFactory();
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(this.iri);
		this.reasoner = new FaCTPlusPlusReasoner(ontology,new SimpleConfiguration(),BufferingMode.BUFFERING);		
		
	}

        public void loadGoal(IRI giri) throws OWLOntologyCreationException
        {
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            OWLOntology ontology = manager.loadOntologyFromOntologyDocument(giri);
	    System.out.println("Axioms:" + ontology.getAxioms());
            Set<OWLAxiom> axioms = ontology.getAxioms();
            //if (axioms.size() == 1)
            //{
                Iterator<OWLAxiom> it = axioms.iterator();
                this.goal = it.next();
            //}
            //else
           // {
             //   throw new OWLOntologyCreationException
              //              ("Too many axioms for conjecture");
           // }
        }

        public boolean prove() throws FaCTPlusPlusException
        {
            if (goal instanceof OWLObjectPropertyAssertionAxiom)
            {
                OWLObjectPropertyAssertionAxiom g =
                        (OWLObjectPropertyAssertionAxiom) goal;
                OWLIndividual object  = g.getObject();
                OWLIndividual subject = g.getSubject();
                OWLObjectPropertyExpression prop = g.getProperty();
		NodeSet<OWLNamedIndividual> ind = reasoner.getObjectPropertyValues (object.asOWLNamedIndividual(),prop);
				
                return ind.containsEntity(subject.asOWLNamedIndividual());
            }
            if (goal instanceof OWLClassAssertionAxiom)
            {
                OWLClassAssertionAxiom g = (OWLClassAssertionAxiom) goal;
                OWLClassExpression cls = g.getClassExpression();
                OWLIndividual indi = g.getIndividual();
		NodeSet<OWLClass> n = reasoner.getTypes(indi.asOWLNamedIndividual(),true);
                return n.containsEntity(cls.asOWLClass());
            }
            if (goal instanceof OWLDataPropertyAssertionAxiom)
            {
                OWLDataPropertyAssertionAxiom g =
                        (OWLDataPropertyAssertionAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                OWLLiteral obj = g.getObject();
                OWLIndividual sub = g.getSubject();
		Set <OWLLiteral> litset = reasoner.getDataPropertyValues(sub.asOWLNamedIndividual(),prop);
                return litset.contains(obj);
            }
            if (goal instanceof OWLEquivalentClassesAxiom)
            {
                OWLEquivalentClassesAxiom g = (OWLEquivalentClassesAxiom) goal;
                OWLClassExpression[] cls = g.getClassExpressions().toArray
                               (new OWLClassExpression[g.getClassExpressions().size()]);
                boolean res = true;
                for (int i=0; i < cls.length; i++)
                {
                    for (int j=0; j < cls.length; j++)
                    {
                        if (i != j)
                        {
			    Node<OWLClass> c = reasoner.getEquivalentClasses(cls[i]);
                            res &= c.contains(cls[j].asOWLClass());
                        }
                    }
                }
                return res;
            }
            if (goal instanceof OWLSubClassOfAxiom)
            {
                OWLSubClassOfAxiom g = (OWLSubClassOfAxiom) goal;
                OWLClassExpression sub = g.getSubClass();
                OWLClassExpression top = g.getSuperClass();
		NodeSet<OWLClass> c = reasoner.getSubClasses(top,true);
                return c.containsEntity(sub.asOWLClass());
            }
            if (goal instanceof OWLDataPropertyRangeAxiom)
            {
                throw new FaCTPlusPlusException
                            ("Fact++ cannot determine data ranges!");
            }
            if (goal instanceof OWLDataPropertyDomainAxiom)
            {
                OWLDataPropertyDomainAxiom g = (OWLDataPropertyDomainAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                OWLClassExpression  d    = g.getDomain();
		boolean res = false;

		NodeSet<OWLClass> dom = reasoner.getDataPropertyDomains(prop,true);
		Iterator<Node<OWLClass>> it = dom.iterator();

		while (it.hasNext())	{
			Node<OWLClass> cur = it.next();
			Iterator<OWLClass> itt = cur.iterator();
			while (itt.hasNext())	{
				OWLClass c = itt.next();
				Node<OWLClass> cl = reasoner.getEquivalentClasses(c);
				if (cl.contains(d.asOWLClass()))
					res = true;
			}
		}				

	        return res;
            }
	    if (goal instanceof OWLSubDataPropertyOfAxiom)
            {
                OWLSubDataPropertyOfAxiom g = (OWLSubDataPropertyOfAxiom) goal;
                OWLDataProperty sub = g.getSubProperty().asOWLDataProperty();
                OWLDataProperty sup = g.getSuperProperty().asOWLDataProperty();
                boolean res = false;
		
		NodeSet<OWLDataProperty> sups = reasoner.getSuperDataProperties(sub,true);
                Iterator<Node<OWLDataProperty>> it = sups.iterator();
                while (it.hasNext())
                {
                    Node<OWLDataProperty> cur = it.next();
                    if (cur.contains(sup)) 
			res = true;
                }
                return res;
            }
            if (goal instanceof OWLAsymmetricObjectPropertyAxiom)
            {
                throw new FaCTPlusPlusException
                            ("Fact++ cannot determine antisymmetry!");
            }
            if (goal instanceof OWLEquivalentDataPropertiesAxiom)
            {
                OWLEquivalentDataPropertiesAxiom g =
                        (OWLEquivalentDataPropertiesAxiom) goal;
                Set<OWLDataPropertyExpression> props = g.getProperties();
                TreeSet<OWLDataProperty> p = new TreeSet<OWLDataProperty>();
                Iterator<OWLDataPropertyExpression> it = props.iterator();
                p.clear();
                while (it.hasNext())
                {
                  p.add(it.next().asOWLDataProperty());
                }
                boolean res = true;
                Iterator<OWLDataProperty> itt = p.iterator();
                while (itt.hasNext())
                {
                    Node<OWLDataProperty> cur = reasoner.getEquivalentDataProperties(itt.next());
		    Set<OWLDataProperty> scur = cur.getEntities();
		    res &= scur.containsAll(props);
                }
                return res;
            }
            if (goal instanceof OWLEquivalentObjectPropertiesAxiom)
            {
                OWLEquivalentObjectPropertiesAxiom g = (OWLEquivalentObjectPropertiesAxiom) goal;
                Set<OWLObjectPropertyExpression> props = g.getProperties();
                TreeSet<OWLObjectPropertyExpression> p = new TreeSet<OWLObjectPropertyExpression>();
                Iterator<OWLObjectPropertyExpression> it = props.iterator();
                p.clear();
                while (it.hasNext())
                {
                  p.add(it.next());
                }
                boolean res = true;
                Iterator<OWLObjectPropertyExpression> itt = p.iterator();
                while (itt.hasNext())
                {
                    Node<OWLObjectPropertyExpression> cur = reasoner.getEquivalentObjectProperties(itt.next());
		    Set<OWLObjectPropertyExpression> scur = cur.getEntities();
                    res &= scur.containsAll(props);
                }
                return res;
            }
            if (goal instanceof OWLFunctionalDataPropertyAxiom)
            {
                OWLFunctionalDataPropertyAxiom g = (OWLFunctionalDataPropertyAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                return prop.isFunctional(reasoner.getRootOntology());
            }
            if (goal instanceof OWLFunctionalObjectPropertyAxiom)
            {
                OWLFunctionalObjectPropertyAxiom g= (OWLFunctionalObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return prop.isFunctional(reasoner.getRootOntology());
            }
            if (goal instanceof OWLInverseFunctionalObjectPropertyAxiom)
            {
                OWLInverseFunctionalObjectPropertyAxiom g =
                        (OWLInverseFunctionalObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return prop.isInverseFunctional(reasoner.getRootOntology());
            }
            if (goal instanceof OWLInverseObjectPropertiesAxiom)
            {
                OWLInverseObjectPropertiesAxiom g = (OWLInverseObjectPropertiesAxiom) goal;
                OWLObjectPropertyExpression fst = g.getFirstProperty();
                OWLObjectPropertyExpression snd = g.getSecondProperty();
                Node<OWLObjectPropertyExpression> is = reasoner.getInverseObjectProperties(fst);
                boolean res = false;
                if (is.contains(snd)) {res=true;}
                return res;
            }
            if (goal instanceof OWLIrreflexiveObjectPropertyAxiom)
            {
                OWLIrreflexiveObjectPropertyAxiom g = (OWLIrreflexiveObjectPropertyAxiom) goal;
                return g.getProperty().asOWLObjectProperty().isIrreflexive(reasoner.getRootOntology());
            }
            if (goal instanceof OWLNegativeDataPropertyAssertionAxiom)
            {
                OWLNegativeDataPropertyAssertionAxiom g = (OWLNegativeDataPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLLiteral   obj = g.getObject();
                OWLDataProperty p = g.getProperty().asOWLDataProperty();
		Set<OWLLiteral> slit = reasoner.getDataPropertyValues(sub.asOWLNamedIndividual(),p);
                return slit.contains(obj);
            }
            if (goal instanceof OWLNegativeObjectPropertyAssertionAxiom)
            {
                OWLNegativeObjectPropertyAssertionAxiom g =
                        (OWLNegativeObjectPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLIndividual obj = g.getObject();
                OWLObjectProperty p = g.getProperty().asOWLObjectProperty();
		
		NodeSet<OWLNamedIndividual> ind = reasoner.getObjectPropertyValues (obj.asOWLNamedIndividual(),p);
				
                return ind.containsEntity(sub.asOWLNamedIndividual());

            }
            if (goal instanceof OWLObjectPropertyAssertionAxiom)
            {
                OWLObjectPropertyAssertionAxiom g =
                        (OWLObjectPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLIndividual obj = g.getObject();
                OWLObjectProperty p = g.getProperty().asOWLObjectProperty();

		NodeSet<OWLNamedIndividual> ind = reasoner.getObjectPropertyValues(obj.asOWLNamedIndividual(),p);
				
                return ind.containsEntity(sub.asOWLNamedIndividual());
            }
            if (goal instanceof OWLObjectPropertyDomainAxiom)
            {
                OWLObjectPropertyDomainAxiom g = (OWLObjectPropertyDomainAxiom) goal;
                OWLObjectPropertyExpression prop = g.getProperty();
                OWLClassExpression    dom  = g.getDomain();
                NodeSet<OWLClass> doms = reasoner.getObjectPropertyDomains(prop,true);
                boolean res = false;
                Iterator<Node<OWLClass>> it = doms.iterator();
                while (it.hasNext())
                {
                    Node<OWLClass> cur = it.next();
                    if (cur.contains(dom.asOWLClass())){res = true;}
                }
                return res;
            }
            if (goal instanceof OWLObjectPropertyRangeAxiom)
            {
                OWLObjectPropertyRangeAxiom g = (OWLObjectPropertyRangeAxiom) goal;
                OWLObjectPropertyExpression prop = g.getProperty();
                OWLClass    ran  = g.getRange().asOWLClass();
                NodeSet<OWLClass>  rns = reasoner.getObjectPropertyRanges(prop,true);
                return rns.containsEntity(ran);
            }
            if (goal instanceof OWLSubObjectPropertyOfAxiom)
            {
                OWLSubObjectPropertyOfAxiom g =
                        (OWLSubObjectPropertyOfAxiom) goal;
                OWLObjectPropertyExpression sub = g.getSubProperty();
                OWLObjectPropertyExpression sup = g.getSuperProperty();
                NodeSet<OWLObjectPropertyExpression> subs = reasoner.getSubObjectProperties(sup,true);
                boolean res = false;
                Iterator<Node<OWLObjectPropertyExpression>> it = subs.iterator();
                while (it.hasNext())
                {
                    Node<OWLObjectPropertyExpression> cur = it.next();
                    if (cur.contains(sub)) {res = true;}
                }
                return res;
            }
            if (goal instanceof OWLReflexiveObjectPropertyAxiom)
            {
                OWLReflexiveObjectPropertyAxiom g = (OWLReflexiveObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return prop.isReflexive(reasoner.getRootOntology());
            }
            if (goal instanceof OWLSymmetricObjectPropertyAxiom)
            {
                OWLSymmetricObjectPropertyAxiom g = (OWLSymmetricObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return prop.isSymmetric(reasoner.getRootOntology());
            }
            if (goal instanceof OWLTransitiveObjectPropertyAxiom)
            {
                OWLTransitiveObjectPropertyAxiom g =
                        (OWLTransitiveObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return prop.isTransitive(reasoner.getRootOntology());
            }
            System.out.println(goal);
            throw new FaCTPlusPlusException
                            ("No reasoner found, sorry!");
        }
}
