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
                return reasoner.hasObjectPropertyRelationship
                        (subject, prop, object);
            }
            if (goal instanceof OWLClassAssertionAxiom)
            {
                OWLClassAssertionAxiom g = (OWLClassAssertionAxiom) goal;
                OWLDescription cls = g.getDescription();
                OWLIndividual indi = g.getIndividual();
                return reasoner.hasType(indi, cls, false);
            }
            if (goal instanceof OWLDataPropertyAssertionAxiom)
            {
                OWLDataPropertyAssertionAxiom g =
                        (OWLDataPropertyAssertionAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                OWLConstant obj      = g.getObject();
                OWLIndividual sub    = g.getSubject();
                return reasoner.hasDataPropertyRelationship(sub, prop, obj);
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
                return reasoner.isSubClassOf(sub, top);
            }
            if (goal instanceof OWLDataPropertyRangeAxiom)
            {
                throw new UnsupportedReasonerOperationException
                            ("Fact++ cannot determine data ranges!");
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
                    Set<OWLDataProperty> cur =
                            reasoner.getEquivalentProperties(itt.next());
                    res &= cur.containsAll(props);
                }
                return res;
            }
            if (goal instanceof OWLEquivalentObjectPropertiesAxiom)
            {
                OWLEquivalentObjectPropertiesAxiom g =
                        (OWLEquivalentObjectPropertiesAxiom) goal;
                Set<OWLObjectPropertyExpression> props = g.getProperties();
                TreeSet<OWLObjectProperty> p = new TreeSet<OWLObjectProperty>();
                Iterator<OWLObjectPropertyExpression> it = props.iterator();
                p.clear();
                while (it.hasNext())
                {
                  p.add(it.next().asOWLObjectProperty());
                }
                boolean res = true;
                Iterator<OWLObjectProperty> itt = p.iterator();
                while (itt.hasNext())
                {
                    Set<OWLObjectProperty> cur =
                            reasoner.getEquivalentProperties(itt.next());
                    res &= cur.containsAll(props);
                }
                return res;
            }
            if (goal instanceof OWLFunctionalDataPropertyAxiom)
            {
                OWLFunctionalDataPropertyAxiom g =
                        (OWLFunctionalDataPropertyAxiom) goal;
                OWLDataProperty prop = g.getProperty().asOWLDataProperty();
                return reasoner.isFunctional(prop);
            }
            if (goal instanceof OWLFunctionalObjectPropertyAxiom)
            {
                OWLFunctionalObjectPropertyAxiom g=
                        (OWLFunctionalObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return reasoner.isFunctional(prop);
            }
            if (goal instanceof OWLInverseFunctionalObjectPropertyAxiom)
            {
                OWLInverseFunctionalObjectPropertyAxiom g =
                        (OWLInverseFunctionalObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return reasoner.isInverseFunctional(prop);
            }
            if (goal instanceof OWLInverseObjectPropertiesAxiom)
            {
                OWLInverseObjectPropertiesAxiom g =
                        (OWLInverseObjectPropertiesAxiom) goal;
                OWLObjectProperty fst =
                        g.getFirstProperty().asOWLObjectProperty();
                OWLObjectProperty snd =
                        g.getSecondProperty().asOWLObjectProperty();
                Set<Set<OWLObjectProperty>> is =
                        reasoner.getInverseProperties(fst);
                boolean res = false;
                Iterator<Set<OWLObjectProperty>> it = is.iterator();
                while (it.hasNext())
                {
                    Set<OWLObjectProperty> cur = it.next();
                    if (cur.contains(snd)) {res=true;}
                }
                return res;
            }
            if (goal instanceof OWLIrreflexiveObjectPropertyAxiom)
            {
                OWLIrreflexiveObjectPropertyAxiom g =
                        (OWLIrreflexiveObjectPropertyAxiom) goal;
                return reasoner.isIrreflexive(g.getProperty().asOWLObjectProperty());
            }
            if (goal instanceof OWLNegativeDataPropertyAssertionAxiom)
            {
                OWLNegativeDataPropertyAssertionAxiom g =
                        (OWLNegativeDataPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLConstant   obj = g.getObject();
                OWLDataProperty p = g.getProperty().asOWLDataProperty();
                return !reasoner.hasDataPropertyRelationship(sub, p, obj);
            }
            if (goal instanceof OWLNegativeObjectPropertyAssertionAxiom)
            {
                OWLNegativeObjectPropertyAssertionAxiom g =
                        (OWLNegativeObjectPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLIndividual obj = g.getObject();
                OWLObjectProperty p = g.getProperty().asOWLObjectProperty();
                return !reasoner.hasObjectPropertyRelationship(sub, p, obj);
            }
            if (goal instanceof OWLObjectPropertyAssertionAxiom)
            {
                OWLObjectPropertyAssertionAxiom g =
                        (OWLObjectPropertyAssertionAxiom) goal;
                OWLIndividual sub = g.getSubject();
                OWLIndividual obj = g.getObject();
                OWLObjectProperty p = g.getProperty().asOWLObjectProperty();
                return reasoner.hasObjectPropertyRelationship(sub, p, obj);
            }
            if (goal instanceof OWLObjectPropertyDomainAxiom)
            {
                OWLObjectPropertyDomainAxiom g =
                        (OWLObjectPropertyDomainAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                OWLDescription    dom  = g.getDomain();
                Set<Set<OWLDescription>> doms = reasoner.getDomains(prop);
                boolean res = false;
                Iterator<Set<OWLDescription>> it = doms.iterator();
                while (it.hasNext())
                {
                    Set<OWLDescription> cur = it.next();
                    if (cur.contains(dom)){res = true;}
                }
                return res;
            }
            if (goal instanceof OWLObjectPropertyRangeAxiom)
            {
                OWLObjectPropertyRangeAxiom g =
                        (OWLObjectPropertyRangeAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                OWLDescription    ran  = g.getRange();
                Set<OWLDescription>  rns = reasoner.getRanges(prop);
                return rns.contains(ran);
            }
            if (goal instanceof OWLObjectSubPropertyAxiom)
            {
                OWLObjectSubPropertyAxiom g =
                        (OWLObjectSubPropertyAxiom) goal;
                OWLObjectProperty sub = g.getSubProperty().asOWLObjectProperty();
                OWLObjectProperty sup = g.getSuperProperty().asOWLObjectProperty();
                Set<Set<OWLObjectProperty>> subs = reasoner.getSubProperties(sup);
                boolean res = false;
                Iterator<Set<OWLObjectProperty>> it = subs.iterator();
                while (it.hasNext())
                {
                    Set<OWLObjectProperty> cur = it.next();
                    if (cur.contains(sub)) {res = true;}
                }
                return res;
            }
            if (goal instanceof OWLReflexiveObjectPropertyAxiom)
            {
                OWLReflexiveObjectPropertyAxiom g =
                        (OWLReflexiveObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return reasoner.isReflexive(prop);
            }
            if (goal instanceof OWLSymmetricObjectPropertyAxiom)
            {
                OWLSymmetricObjectPropertyAxiom g =
                        (OWLSymmetricObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return reasoner.isSymmetric(prop);
            }
            if (goal instanceof OWLTransitiveObjectPropertyAxiom)
            {
                OWLTransitiveObjectPropertyAxiom g =
                        (OWLTransitiveObjectPropertyAxiom) goal;
                OWLObjectProperty prop = g.getProperty().asOWLObjectProperty();
                return reasoner.isTransitive(prop);
            }
            System.out.println(goal);
            throw new UnsupportedReasonerOperationException
                            ("No reasoner found, sorry!");
        }
}
