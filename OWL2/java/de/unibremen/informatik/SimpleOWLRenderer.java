import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.io.OWLRendererException;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxObjectRenderer;
import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;

import java.io.*;
import java.net.URI;
import java.util.*;


//@SuppressWarnings("unchecked")
public class OWL2Parser {

	public static void main(String[] args) {

		if (args.length < 1) {
			System.out.println("Usage: processor <URI> [FILENAME]");
			System.exit(1);
		}

		String filename = "";
		BufferedWriter out;
                boolean OP = false;

		// A simple example of how to load and save an ontology
		try {
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			if (args.length == 3) {
				filename = args[1];
				out = new BufferedWriter(new FileWriter(filename));
				if (args[2].equals("xml"))
					OP = true;

			} else {
				if (args.length == 2)	{
					if (args[1].equals("xml"))
						OP = true;
				}
				out = new BufferedWriter(new OutputStreamWriter(System.out));
			}

			/* Load an ontology from a physical IRI */
			IRI physicalIRI = IRI.create(args[0]);

			// Now do the loading

			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);

			if (OP)
                            parse2xml(ontology, out, manager);
                        else
                            parse(ontology, out, manager);
		} catch (IOException e) {
			System.err.println("Error: can not build file: " + filename);
			e.printStackTrace();
		} catch (Exception ex) {
			System.err.println("OWL parse error: " + ex.getMessage());
			ex.printStackTrace();
		}
	}

        public static void parse(OWLOntology onto, BufferedWriter out, OWLOntologyManager mng)
        {
		try {
                    ManchesterOWLSyntaxRenderer ren = new ManchesterOWLSyntaxRenderer (mng);
		ren.render(onto, out);
		} catch(OWLRendererException ex)	{
			System.err.println("Error by parse!");
			ex.printStackTrace();
		}
	}

	public static void parse2xml(OWLOntology onto, BufferedWriter out, OWLOntologyManager mng)
        {
		try {
		OWLXMLRenderer ren = new OWLXMLRenderer(mng);
		ren.render(onto, out);
		} catch (OWLRendererException ex)	{
			System.err.println("Error by XMLParser!");
			ex.printStackTrace();
		}
	}
}
