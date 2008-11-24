package de.unibremen.informatik.locality;

import com.clarkparsia.modularity.locality.LocalityClass;
import com.clarkparsia.modularity.locality.LocalityEvaluator;
import com.clarkparsia.modularity.locality.SyntacticLocalityEvaluator;

import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.io.OWLXMLOntologyFormat;
import org.semanticweb.owl.model.*;

import java.net.URI;

import java.util.Set;

public class LocalityChecker {

    private static Set<? extends OWLEntity> sign;

    public static void main(String[] args)
    {
	if (args.length < 1) 
	    {
		System.out.println("Usage: LocalityChecker <URI> <Class*>");
		System.exit(1);
	    }

	try
	    {
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		URI physicalURI = URI.create(args[0]);
		OWLOntology ontology = 
		    manager.loadOntologyFromPhysicalURI(physicalURI);
	    }
	catch (OWLOntologyCreationException e)
	    {
		System.out.println("The ontology could not be created: " + 
				   e.getMessage());
	    }
    }

}
