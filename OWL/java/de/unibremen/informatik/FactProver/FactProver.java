package de.unibremen.informatik.FactProver;

import uk.ac.manchester.cs.factplusplus.owlapi.*;
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
	
	public FactProver(URI uri) throws OWLOntologyCreationException,
                                          OWLReasonerException
	{
		this.uri = uri;
		OWLOntologyManager manager = 
		    OWLManager.createOWLOntologyManager();
		OWLReasonerFactory fac = new FaCTPlusPlusReasonerFactory();
		OWLReasoner reasoner = fac.createReasoner(manager);
		OWLOntology ontology = 
		    manager.loadOntologyFromPhysicalURI(this.uri);
		TreeSet ontos = new TreeSet();
		ontos.add(ontology);
		reasoner.loadOntologies(ontos);
	}
	
}
