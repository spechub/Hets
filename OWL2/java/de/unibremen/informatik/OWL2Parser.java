import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.io.OWLRendererException;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxObjectRenderer;
import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.coode.owlapi.rdf.rdfxml.*;
import org.coode.owlapi.rdf.model.*;

import java.io.*;
import java.net.URI;
import java.util.*;

//@SuppressWarnings("unchecked")
public class OWL2Parser {
	private static enum OPTION {OWL_XML, MANCHESTER, RDF_XML}
	private static OPTION op;
	private static List<OWLOntology> loadedImportsList = new ArrayList<OWLOntology>();
	private static ArrayList<IRI> importsIRI = new ArrayList<IRI>();
	private static Map<OWLOntology,List<OWLOntology>> m = new HashMap<OWLOntology, List<OWLOntology>>();
	private static Set<OWLOntology> s = new HashSet<OWLOntology>();
	private static Set<OWLOntology> expanded = new HashSet<OWLOntology>();

	public static void main(String[] args) {

		if (args.length < 1) {
			System.out.println("Usage: processor <URI> [FILENAME] <OPTION>");
			System.exit(1);
		}

		String filename = "";
		BufferedWriter out;

		// A simple example of how to load and save an ontology
		try {
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			if (args.length == 3) {
                                // args[0]: IRI
                                // args[1]: name of output file
                                // args[2]: type of output file: xml, rdf, or otherwise assume Manchester syntax
				filename = args[1];
				out = new BufferedWriter(new FileWriter(filename));
				if (args[2].equals("xml"))
					op = OPTION.OWL_XML;
				else	{
						if (args[1].equals("rdf"))
							op = OPTION.RDF_XML;
						else
							op = OPTION.MANCHESTER;
					}

			} else {
                                // args[0]: IRI
                                // args[1]: type of output:
                                //   xml (OWL XML),
                                //   rdf (RDF/XML),
                                //   or otherwise use Manchester syntax
                                // Output goes to standard output, i.e. System.out
				if (args.length == 2) {
					if (args[1].equals("xml"))
						op = OPTION.OWL_XML;
					else	{
						if (args[1].equals("rdf"))
							op = OPTION.RDF_XML;
						else
							op = OPTION.MANCHESTER;			
					}
				}
				else 
				{
                                        // args[0]: IRI
                                        // Output goes to standard output, i.e. System.out
                                        // and will be made in Manchester syntax
					if (args.length == 1)
						op = OPTION.MANCHESTER;
				}
				out = new BufferedWriter(new OutputStreamWriter(System.out));
			}

			/* Load an ontology from a physical IRI */
			IRI physicalIRI = IRI.create(args[0]);
	//		System.out.println("IRI: " + physicalIRI + "\n");

			// Now do the loading
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);
			getImportsList(ontology, manager);

			if (loadedImportsList.size() == 0)			
				parsing_option(ontology, out, manager);
			else {
				if(importsIRI.contains(ontology.getOntologyID().getOntologyIRI())) {
    					importsIRI.remove(importsIRI.lastIndexOf(ontology.getOntologyID().getOntologyIRI()));
					}
				if(loadedImportsList.contains(ontology)) {

					OWLOntologyManager mng = OWLManager.createOWLOntologyManager();
					OWLOntologyMerger merger = new OWLOntologyMerger(manager);

					String str = ontology.getOntologyID().getOntologyIRI().toQuotedString();
					String notag = str.replaceAll("\\<","");

					notag = notag.replaceAll("\\>","");
					notag = notag.replaceAll("\\[.*?]","");
					notag = notag.replaceAll("Ontology\\(","");
					notag = notag.replaceAll(" ","");
					notag = notag.replaceAll("\\)","");

					loadedImportsList.remove(loadedImportsList.indexOf(ontology));
					Object aux[] = loadedImportsList.toArray();

					String merged_name = "";

					for (Object it : aux) {
						Object aux_ont = it;
						String mrg = aux_ont.toString();
						mrg = mrg.replaceAll("\\>","");
						mrg = mrg.replaceAll("http:/","");
						mrg = mrg.replaceAll("\\/.*?/","");
						mrg = mrg.replaceAll(".*?/","");
						mrg = mrg.replaceAll("\\[.*?]","");
						mrg = mrg.replaceAll("\\)","");
						mrg = mrg.replaceAll(" ","");
						merged_name = merged_name + mrg;
					}

					merged_name = notag + merged_name;
			//		System.out.println("NAME: " + merged_name + "\n");
					IRI mergedOntologyIRI = IRI.create(merged_name);
			//		System.out.println("MERGED_IRI " + mergedOntologyIRI + "\n");
					OWLOntology merged = merger.createMergedOntology(manager, mergedOntologyIRI);

					ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer (manager);
				//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
					parsing_option(merged, out, manager);
				}
				else	
					parseZeroImports(out, ontology);
			}
		} catch (IOException e) {
			System.err.println("Error: can not build file: " + filename);
			e.printStackTrace();
		} catch (Exception ex) {
			System.err.println("OWL parse error: " + ex.getMessage());
			ex.printStackTrace();
		}
	}

	private static void getImportsList(OWLOntology ontology,
			OWLOntologyManager om) {

		List<OWLOntology> empty = Collections.emptyList();
		List<OWLOntology> l = new ArrayList<OWLOntology>();
		ArrayList<OWLOntology> unSavedImports = new ArrayList<OWLOntology>();

		try {
			if (om.getDirectImports(ontology).isEmpty()) {
				m.put(ontology,empty);
			}
			else {
				List<OWLOntology> srt = new ArrayList<OWLOntology>();
				for (OWLOntology imported : om.getDirectImports(ontology)) {
					if (!importsIRI.contains(imported.getOntologyID().getOntologyIRI())) {
						unSavedImports.add(imported);
						loadedImportsList.add(imported);
						importsIRI.add(imported.getOntologyID().getOntologyIRI());
						l.add(imported);
					}
				}
			}
			m.put(ontology,l);
			for (OWLOntology onto : unSavedImports) {
				getImportsList(onto, om);
			}

		} catch (Exception e) {
			System.err.println("Error getImportsList!");
			e.printStackTrace();
		}
	}

	private static void parseZeroImports(BufferedWriter out, OWLOntology ontology) 	{
		List all = getKeysByValue();
		ListIterator it = all.listIterator();
		ListIterator itr = all.listIterator();

		while(itr.hasNext()) {
			OWLOntology ontos = (OWLOntology)itr.next();
			expanded.add(ontos);
			parsing_option(ontos, out, ontos.getOWLOntologyManager());
			s.add(ontos);
			parseImports(out, ontology);
		}
	}


	public static void parseImports(BufferedWriter out, OWLOntology ontology) {

		Iterator iter = m.entrySet().iterator();
		while (iter.hasNext())  {

			Map.Entry pairs = (Map.Entry)iter.next();
			Set values = new HashSet<OWLOntology>();
			List ls = new ArrayList<OWLOntology>();
			ls.add(pairs.getValue());
			List l = new ArrayList<OWLOntology>();
			l = (List)ls.get(0);
			values = cnvrt(l);
			OWLOntology onto = (OWLOntology)pairs.getKey();

			if(checkset(values)) {
				if (!expanded.contains(onto))
					{
					parsing_option (onto, out, onto.getOWLOntologyManager());
					expanded.add(onto);
					s.add((OWLOntology)pairs.getKey());
					if (onto.getOntologyID().toString().equals(ontology.getOntologyID().toString()))
						System.exit(0);

					parseImports(out, ontology);
				}
			}
		}
	}

	public static Set cnvrt(List lst) {

		Set st = new HashSet<OWLOntology>();
		Iterator it = lst.iterator();

		if (lst.size() == 0)
			return st;

		while(it.hasNext()) {
			OWLOntology aux_ont = (OWLOntology)it.next();
			st.add(aux_ont);
		}
		return st;
	}

	public static Boolean checkset(Collection it) {

		if (it.isEmpty()) return false;
		Set<OWLOntology> aux = new HashSet<OWLOntology>();
		aux.addAll(it);
		return equalcollections(aux, s);
	}

	public static Boolean equalcollections(Set<OWLOntology> l1, Set<OWLOntology> l2) {
		Boolean eq = true;

		if(l1.isEmpty() || l2.isEmpty())
			eq = false;

		for (OWLOntology ont: l1)
			if (!l2.contains(ont))
				eq = false;
		return eq;
	}

	public static List getKeysByValue() {
		List keys = new ArrayList<OWLOntology>();
		Iterator it = m.entrySet().iterator();
		while(it.hasNext()) {
			Map.Entry pairs = (Map.Entry)it.next();
			if(pairs.getValue().toString().equals("[]")) {
				keys.add(pairs.getKey());
			}
		}
     	return keys;
	}

	public static void parsing_option(OWLOntology onto, BufferedWriter out, OWLOntologyManager mng) {
		switch (op) {
			case OWL_XML: parse2xml(onto, out, mng); 	break;
			case MANCHESTER: parse(onto, out); 			break;
			case RDF_XML: parse2rdf(onto, out, mng);	break;
		}
	}

	public static void parse(OWLOntology onto, BufferedWriter out)	{
		try {
		ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer (onto.getOWLOntologyManager());
		rendi.render(onto,out);
		} catch(OWLRendererException ex) {
			System.err.println("Error by ManchesterParser!");
			ex.printStackTrace();
		}
	}

	public static void parse2xml(OWLOntology onto, BufferedWriter out, OWLOntologyManager mng) {
		try {
		OWLXMLRenderer ren = new OWLXMLRenderer(mng);
		ren.render(onto,out);
		} catch (OWLRendererException ex)	{
			System.err.println("Error by XMLParser!");
			ex.printStackTrace();
		}
	}

	public static void parse2rdf(OWLOntology onto, BufferedWriter out, OWLOntologyManager mng) {
		try {
			RDFXMLRenderer rdfrend = new RDFXMLRenderer(mng, onto, out);
			rdfrend.render();
		} catch (IOException ex) {
			System.err.println("Error by RDFParser!");
			ex.printStackTrace();
		}
	}
}
