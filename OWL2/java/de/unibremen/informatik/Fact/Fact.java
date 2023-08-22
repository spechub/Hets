package de.unibremen.informatik.Fact;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import uk.ac.manchester.cs.factplusplus.owlapiv3.FaCTPlusPlusReasonerFactory;

class Fact {
	public static void main(String[] args) {
		if (args.length < 1) {
			System.out.println("owl_fact <Ontology>");
			System.exit(1);
		}
		try {
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			FaCTPlusPlusReasonerFactory f = new FaCTPlusPlusReasonerFactory();
			IRI physicalIRI = IRI.create(args[0]);
			OWLOntology ontology =
				manager.loadOntologyFromOntologyDocument(physicalIRI);
			OWLReasoner reasoner = f.createReasoner(ontology);
			Boolean cons = reasoner.isConsistent();
			if (cons) {
				System.out.println("consistent");
				System.exit(10);
			} else {
				System.out.println("inconsistent");
				System.exit(20);
			}
		} catch (OWLOntologyCreationException e) {
			System.out.println("The ontology could not be created: "
				+ e.getMessage());
			System.exit(1);
		} catch (Exception e) {
			System.out.println("Exception:" + e.getMessage());
			System.exit(1);
		}
	}
}
