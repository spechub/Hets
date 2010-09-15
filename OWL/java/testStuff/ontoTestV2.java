import com.clarkparsia.modularity.locality.LocalityClass;
import com.clarkparsia.modularity.locality.LocalityEvaluator;
import com.clarkparsia.modularity.locality.SyntacticLocalityEvaluator;

import org.semanticweb.owl.apibinding.OWLManager;
import org.semanticweb.owl.io.OWLXMLOntologyFormat;
import org.semanticweb.owl.model.*;

import java.net.URI;

import java.util.Set;
import java.util.Iterator;

import org.semanticweb.owl.io.ToStringRenderer;

public  class ontoTestV2 {

    private static Set<OWLAxiom> axioms;
    private static ToStringRenderer out;

    public static void main(String[] args) {
	try {
	    loader(args[0]);
	    out = org.semanticweb.owl.io.ToStringRenderer.getInstance();
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
	URI physicalURI = URI.create(onto);
	OWLOntology ontology = 
	    manager.loadOntologyFromPhysicalURI(physicalURI);
	axioms = ontology.getAxioms();
    }
}
