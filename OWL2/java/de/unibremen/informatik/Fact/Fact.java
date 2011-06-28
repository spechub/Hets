package de.unibremen.informatik.Fact;

import uk.ac.manchester.cs.factplusplus.owlapiv3.*;
import org.semanticweb.owlapi.reasoner.*;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.semanticweb.HermiT.Reasoner;

import java.net.URI;
import java.util.*;

class Fact
{

    public static void main (String[] args)
    {
	if (args.length < 1) 
	    {
		System.out.println("owl_fact <Ontology>");
		System.exit(1);
	    }

	try
	    {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		IRI physicalIRI = IRI.create(args[0]);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);
	
		OWLReasonerFactory reasonerFa = new Reasoner.ReasonerFactory();
	
		OWLReasoner reasoner = reasonerFa.createReasoner(ontology);

		//reasoner.precomputeInferences();
	
		Boolean cons = reasoner.isConsistent();
		if (cons)
		    {
			System.out.println("consistent");
			System.exit(10);
		    }
		else
		    {
			System.out.println("inconsistent");
			System.exit(20);
		    }
	    }
	catch (OWLOntologyCreationException e)
	    {
		System.out.println("The ontology could not be created: " + 
				   e.getMessage());
		System.exit(1);
	    }
	catch (Exception e)
	    {
		System.out.println("Exception:" + e.getMessage());
		System.exit(1);
	    }
	
    }

}
