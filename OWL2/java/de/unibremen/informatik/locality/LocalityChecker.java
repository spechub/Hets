package de.unibremen.informatik.locality;

import java.util.Iterator;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLObjectRenderer;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import com.clarkparsia.owlapi.modularity.locality.LocalityClass;
import com.clarkparsia.owlapi.modularity.locality.SyntacticLocalityEvaluator;

public class LocalityChecker {
	private static Set<OWLEntity> sign;
	private static Set<OWLAxiom> axioms;

	public static void main(String[] args) {
		if (args.length != 3) {
			System.out.println("Usage: LocalityChecker <URI> "
				+ "<SignatureURI> <LocalityType>");
			System.exit(1);
		}
		LocalityClass cl = LocalityClass.BOTTOM_BOTTOM;
		if (args[2].equals("TOP_BOTTOM")) {
			cl = LocalityClass.TOP_BOTTOM;
		} else if (args[2].equals("TOP_TOP")) {
			cl = LocalityClass.TOP_TOP;
		} else {
			cl = LocalityClass.BOTTOM_BOTTOM;
		}
		try {
			loader(args[0], args[1]);
			// print();
			boolean local = checker(cl);
			System.out.print("Result: ");
			if (local) {
				System.out.println("LOCAL");
				System.exit(10);
			} else {
				System.out.println("NON-LOCAL");
				System.exit(20);
			}
		} catch (OWLOntologyCreationException e) {
			System.out.println("The ontology could not be created: "
				+ e.getMessage());
			System.exit(1);
		}
	}

	private static Boolean checker(LocalityClass cl) {
		boolean local = true;
		OWLObjectRenderer out = org.semanticweb.owlapi.io.ToStringRenderer.getInstance();
		SyntacticLocalityEvaluator eval = new SyntacticLocalityEvaluator(cl);
		// let's try the bottom evaluator first
		Iterator<OWLAxiom> it = axioms.iterator();
		while (it.hasNext()) {
			OWLAxiom elem = it.next();
			boolean l = eval.isLocal(elem, sign);
			if (!l) {
				System.out.print("Non-local axiom: ");
				System.out.println(out.render(elem));
				System.out.println("");
			}
			local = local && l;
		}
		return local;
	}

	private static void print() {
		System.out.println("Axioms:");
		Iterator<OWLAxiom> it = axioms.iterator();
		while (it.hasNext()) {
			OWLAxiom elem = it.next();
			System.out.println(elem);
		}
		System.out.println("\nSignature:");
		Iterator<OWLEntity> itE = sign.iterator();
		while (itE.hasNext()) {
			OWLEntity elemE = itE.next();
			System.out.println(elemE);
		}
	}

	private static void loader(String onto, String sig)
		throws OWLOntologyCreationException
	{
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntologyManager signMan = OWLManager.createOWLOntologyManager();
		IRI physicalIRI = IRI.create(onto);
		IRI signIRI = IRI.create(sig);
		OWLOntology ontology =
			manager.loadOntologyFromOntologyDocument(physicalIRI);
		OWLOntology signOnto =
			manager.loadOntologyFromOntologyDocument(signIRI);
		sign = signOnto.getSignature();
		axioms = ontology.getAxioms();
	}
}
