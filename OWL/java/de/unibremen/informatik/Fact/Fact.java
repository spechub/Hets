package de.unibremen.informatik.Fact;

import uk.ac.manchester.cs.factplusplus.owlapi.*;

import org.semanticweb.owl.inference.*;

import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.io.OWLXMLOntologyFormat;
import org.semanticweb.owl.model.*;
import java.net.URI;

class Fact
{

    public static void main (String[] args)
    {
	try
	    {
		OWLOntologyManager manager = 
		    OWLManager.createOWLOntologyManager();
		OWLReasoner reasoner = new Reasoner(manager);
		URI physicalURI = URI.create(args[0]);
		OWLOntology ontology = 
		    manager.loadOntologyFromPhysicalURI(physicalURI);
		Boolean cons = reasoner.isConsistent(ontology);
		System.out.println(cons);
	    }
	catch (OWLOntologyCreationException e)
	    {
		System.out.println("The ontology could not be created: " + 
				   e.getMessage());
		System.exit(1);
	    }
	catch (Exception e)
	    {
		System.out.println("Exception: " + 
				   e.getMessage());
		System.exit(1);
	    }
    }

}
