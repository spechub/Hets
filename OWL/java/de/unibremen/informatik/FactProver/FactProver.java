package de.unibremen.informatik.FactProver;

import uk.ac.manchester.cs.factplusplus.*;
import org.semanticweb.reasonerfactory.factpp.*;

import org.semanticweb.owl.inference.*;

import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.io.OWLXMLOntologyFormat;
import org.semanticweb.owl.model.*;
import java.net.URI;
import java.util.*;

public class FactProver 
{

	private URI uri;
	private OWLReasoner reasoner;
        private OWLObject goal;

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
            throw new UnsupportedReasonerOperationException
                            ("No reasoner found, sorry!");
        }
}
