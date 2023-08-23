package de.unibremen.informatik.FactProver;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;

public class Prove {

	public static void main(String[] args) {
		if (args.length < 2) {
			System.out.println("owl_fact_prover <Ontology> <Conjecture>");
			System.exit(1);
		}
		try {
			IRI physicalIRI = IRI.create(args[0]);
			IRI goalIRI = IRI.create(args[1]);
			FactProver prover = new FactProver(physicalIRI);
			System.out.println("FactProver: " + prover + "\n");
			System.out.println("PhysicalIRI: " + physicalIRI + "\n");
			System.out.println("GoalIRI: " + goalIRI + "\n");
			prover.loadGoal(goalIRI);
			boolean res = prover.prove();
			if (res) {
				System.out.println("proved");
				System.exit(10);
			} else {
				System.out.println("disproved");
				System.exit(20);
			}
		} catch (InconsistentOntologyException e) {
			System.out.println("inconsistent");
			System.exit(30);
		} catch (Exception e) {
			System.out.println(e.getMessage());
			System.exit(1);
		}
	}
}
