package de.unibremen.informatik.locality;

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

public class LocalityChecker {

    private static Set<OWLEntity> sign;
    private static Set<OWLAxiom> axioms;
    private static ToStringRenderer out;

    public static void main(String[] args)
    {
	if (args.length != 2) 
	    {
		System.out.println("Usage: LocalityChecker <URI> " +
                                   "<SignatureURI>");
		System.exit(1);
	    }

	try 
	    {
		loader(args[0], args[1]);
		//print();
		boolean local = checker();
		System.out.print("Result: ");
		if (local)
		    {
			System.out.println("LOCAL");
			System.exit(10);
		    }
		else
		    {
			System.out.println("NON-LOCAL");
			System.exit(20);			
		    }
	    }
	catch (OWLOntologyCreationException e)
	    {
		System.out.println("The ontology could not be created: " + 
				   e.getMessage());
		System.exit(1);
	    }
    }

    private static Boolean checker()
    {
	boolean local = true;
	out = org.semanticweb.owl.io.ToStringRenderer.getInstance();
	SyntacticLocalityEvaluator eval = 
	    new SyntacticLocalityEvaluator(com.clarkparsia.modularity.locality.LocalityClass.BOTTOM_BOTTOM); 
	//let's try the bottom evaluator first
	Iterator<OWLAxiom> it = axioms.iterator();
	while (it.hasNext())
	    {
		OWLAxiom elem = it.next();
		boolean l = eval.isLocal(elem, sign);
		if (!l)
		    {
			System.out.print("Non-local axiom: ");
			System.out.println(out.getRendering(elem));
			System.out.println("");
		    }
		local = local && l;
	    }
	return local;
    }

    private static void print()
    {
	System.out.println("Axioms:");
	Iterator<OWLAxiom> it = axioms.iterator();
	while (it.hasNext())
	    {
		OWLAxiom elem = it.next();
		System.out.println(elem); 
	    }
	System.out.println("\nSignature:");
	Iterator<OWLEntity> itE = sign.iterator();
	while (itE.hasNext())
	    {
		OWLEntity elemE = itE.next();
		System.out.println(elemE); 
	    }	
    }

    private static void loader(String onto, String sig) throws OWLOntologyCreationException
    {
	OWLOntologyManager manager = 
	    OWLManager.createOWLOntologyManager();
	OWLOntologyManager signMan = 
	    OWLManager.createOWLOntologyManager();
	URI physicalURI = URI.create(onto);
	URI signURI     = URI.create(sig);
	OWLOntology ontology = 
	    manager.loadOntologyFromPhysicalURI(physicalURI);
	OWLOntology signOnto = 
	    manager.loadOntologyFromPhysicalURI(signURI);
	sign = signOnto.getSignature();
	axioms = ontology.getAxioms();
    }
    
}
