import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.*;

import java.util.Set;
import java.util.Iterator;

import org.semanticweb.owlapi.io.ToStringRenderer;

public  class ontoTestV3 {

    private static Set<OWLAxiom> axioms;
    private static ToStringRenderer out;

    public static void main(String[] args) {
	try {
	    loader(args[0]);
	    out = org.semanticweb.owlapi.io.ToStringRenderer.getInstance();
	    Iterator<OWLAxiom> it = axioms.iterator();
	    while (it.hasNext()) {
		System.out.println(out.getRendering(it.next()));
	    }
	}
	catch (OWLOntologyCreationException e) {
	    System.out.println("Could not create ontology");
	    e.printStackTrace();
	    System.exit(1);
	}
    }

    private static void loader(String onto) throws OWLOntologyCreationException
    {
	OWLOntologyManager manager = 
	    OWLManager.createOWLOntologyManager();
	IRI physicalURI = IRI.create(onto);
	OWLOntology ontology = 
	    manager.loadOntologyFromOntologyDocument(physicalURI);
	axioms = ontology.getAxioms();
    }
}
