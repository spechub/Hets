package de.unibremen.informatik.FactProver;

import org.semanticweb.reasonerfactory.factpp.*;

import org.semanticweb.owl.inference.*;

import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.model.*;
import java.net.URI;
import java.util.*;

public class FactProver 
{

	private URI uri;
	private OWLReasoner reasoner;
        private OWLAxiom goal;

	public FactProver(URI uri) throws OWLOntologyCreationException,
                                          OWLReasonerException
	{
		this.uri = uri;
		OWLOntologyManager manager = 
		    OWLManager.createOWLOntologyManager();
		OWLReasonerFactory fac = new FaCTPlusPlusReasonerFactory();
		this.reasoner = fac.createReasoner(manager);
		OWLOntology ontology = 
		    manager.loadOntologyFromPhysicalURI(this.uri);
		TreeSet ontos = new TreeSet();
		ontos.add(ontology);
		this.reasoner.loadOntologies(ontos);
	}

        public void loadGoal(URI guri) throws OWLOntologyCreationException
        {
            OWLOntologyManager manager =
		    OWLManager.createOWLOntologyManager();
            OWLOntology ontology =
		    manager.loadOntologyFromPhysicalURI(guri);
            Set<OWLAxiom> axioms = ontology.getAxioms();
            if (axioms.size() == 1)
            {
                Iterator<OWLAxiom> it = axioms.iterator();
                this.goal = it.next();
            }
            else
            {
                throw new OWLOntologyCreationException
                            ("Too many axioms for conjecture");
            }
        }

        public boolean prove() throws OWLReasonerException
        {
            if (goal instanceof OWLObjectPropertyAssertionAxiom)
            {
                OWLObjectPropertyAssertionAxiom g =
                        (OWLObjectPropertyAssertionAxiom) goal;
                OWLIndividual object  = g.getObject();
                OWLIndividual subject = g.getSubject();
                OWLObjectPropertyExpression prop = g.getProperty();
                boolean res = reasoner.hasObjectPropertyRelationship
                        (subject, prop, object);
                return res;
            }
            if (goal instanceof OWLClassAssertionAxiom)
            {
                OWLClassAssertionAxiom g = (OWLClassAssertionAxiom) goal;
                OWLDescription cls = g.getDescription();
                OWLIndividual indi = g.getIndividual();
                boolean res = reasoner.hasType(indi, cls, false);
                return res;
            }
            if (goal instanceof OWLDataPropertyAssertionAxiom)
            {
                OWLDataPropertyAssertionAxiom g =
                        (OWLDataPropertyAssertionAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                OWLConstant obj      = g.getObject();
                OWLIndividual sub    = g.getSubject();
                boolean res = reasoner.hasDataPropertyRelationship(sub, prop, obj);
                return res;
            }
            if (goal instanceof OWLEquivalentClassesAxiom)
            {
                OWLEquivalentClassesAxiom g = (OWLEquivalentClassesAxiom) goal;
                OWLDescription[] cls = g.getDescriptions().toArray
                               (new OWLDescription[g.getDescriptions().size()]);
                boolean res = true;
                for (int i=0; i < cls.length; i++)
                {
                    for (int j=0; j < cls.length; j++)
                    {
                        if (i != j)
                        {
                            res &= reasoner.isEquivalentClass(cls[i], cls[j]);
                        }
                    }
                }
                return res;
            }
            if (goal instanceof OWLSubClassAxiom)
            {
                OWLSubClassAxiom g = (OWLSubClassAxiom) goal;
                OWLDescription sub = g.getSubClass();
                OWLDescription top = g.getSuperClass();
                boolean res = reasoner.isSubClassOf(sub, top);
                return res;
            }
            if (goal instanceof OWLDataPropertyRangeAxiom)
            {
                throw new UnsupportedReasonerOperationException
                            ("Fact++ cannot determine data ranges!");
            }
            if (goal instanceof OWLDataPropertyCharacteristicAxiom)
            {
                OWLDataPropertyCharacteristicAxiom g =
                    (OWLDataPropertyCharacteristicAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                boolean res = reasoner.isFunctional(prop);
                return res;
            }
            if (goal instanceof OWLDataPropertyDomainAxiom)
            {
                OWLDataPropertyDomainAxiom g =
                        (OWLDataPropertyDomainAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                OWLDescription  d    = g.getDomain();
                Set<Set<OWLDescription>> dom = reasoner.getDomains(prop);
                Iterator<Set<OWLDescription>> it = dom.iterator();
                boolean res = false;
                while (it.hasNext())
                {
                    Set<OWLDescription> cur = it.next();
                    Iterator<OWLDescription> itt = cur.iterator();
                    while (itt.hasNext())
                    {
                        OWLDescription c = itt.next();
                        if (reasoner.isEquivalentClass(d, c)) {res=true;}
                    }
                }
                return res;
            }
            if (goal instanceof OWLDataSubPropertyAxiom)
            {
                OWLDataSubPropertyAxiom g =
                        (OWLDataSubPropertyAxiom) goal;
                OWLDataProperty sub = g.getSubProperty().asOWLDataProperty();
                OWLDataProperty sup = g.getSuperProperty().asOWLDataProperty();
                Set<Set<OWLDataProperty>> sups = reasoner.getSuperProperties(sub);
                boolean res = false;
                Iterator<Set<OWLDataProperty>> it = sups.iterator();
                while (it.hasNext())
                {
                    Set<OWLDataProperty> cur = it.next();
                    if (cur.contains(sup)) {res = true;}
                }
                return res;
            }
            if (goal instanceof OWLAntiSymmetricObjectPropertyAxiom)
            {
                throw new UnsupportedReasonerOperationException
                            ("Fact++ cannot determine antisymmetry!");
            }
            System.out.println(goal);
            throw new UnsupportedReasonerOperationException
                            ("No reasoner found, sorry!");
        }
}
