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

import java.io.BufferedReader;
import java.io.PrintWriter;
import java.io.OutputStreamWriter;
import java.io.File;
import java.io.Writer;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URI;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.net.URLConnection;
import java.util.Iterator;
import java.util.HashMap;
import java.util.Map;

@SuppressWarnings("unchecked")
public class OWL2Parser {

	private static ArrayList<OWLOntology> loadedImportsList = new ArrayList<OWLOntology>();
	private static ArrayList<IRI> importsIRI = new ArrayList<IRI>();
	private static ArrayList<OWLOntology> haveImportsList = new ArrayList<OWLOntology>();
	private static Map m = new HashMap();  
	private static Set s = new HashSet();

	public static void main(String[] args) {
		
		if (args.length < 1) {
			System.out.println("Usage: processor <URI> [FILENAME]");
			System.exit(1);
		}

		String filename = "";
		BufferedWriter out;
		
		// A simple example of how to load and save an ontology
		try {
			IRI iri = IRI.create(args[0]);
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			if (args.length == 2) {
				filename = args[1];
				out = new BufferedWriter(new FileWriter(filename));
			} else {
				out = new BufferedWriter(openForFile(null));
			}
						
			/* Load an ontology from a physical IRI */
			IRI physicalIRI = IRI.create(args[0]);
						
			// Now do the loading
			
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);

			getImportsList(ontology, manager);
	
			if(loadedImportsList.size() == 0)
			{
				parse(ontology,out);
			}	

			else {
				if(importsIRI.contains(ontology.getOntologyID().getOntologyIRI())) {
    					importsIRI.remove(importsIRI.lastIndexOf(ontology.getOntologyID().getOntologyIRI()));
					}
				
				if(loadedImportsList.contains(ontology))
					{	

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
					
					IRI mergedOntologyIRI = IRI.create(merged_name);
					OWLOntology merged = merger.createMergedOntology(manager, mergedOntologyIRI);
					
					ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer (manager);
					rendi.render(merged,out);
					}
				else 	
					{
					parseZeroImports(out);
					}
   			
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

		ArrayList<OWLOntology> unSavedImports = new ArrayList<OWLOntology>();
		
		try {	
			if (om.getImports(ontology).isEmpty())	{
				m.put(ontology,0); 
			}
			else 	{ 
				haveImportsList.add(ontology);
	
				for (OWLOntology imported : om.getImports(ontology)) {
					if (!importsIRI.contains(imported.getOntologyID().getOntologyIRI())) {
	
						unSavedImports.add(imported);
						loadedImportsList.add(imported);
						importsIRI.add(imported.getOntologyID().getOntologyIRI());
	
						if(!loadedImportsList.contains(ontology))	{
							m.put(ontology,imported);
						}
					}
				}
				} 				
					
			for (OWLOntology onto : unSavedImports) {
				getImportsList(onto, om);
			}

		} catch (Exception e) {
			System.err.println("Error getImportsList!");
			e.printStackTrace();
		}
	}

	private static Writer openForFile(String fileName) 
		{ 		
			return new OutputStreamWriter(System.out);
		}
	
	private static void parseZeroImports(BufferedWriter out) 
	{
		Set all = getKeysByValue(0);
		Iterator it = all.iterator();
		
		while(it.hasNext())	
			{
			OWLOntology onto = (OWLOntology)it.next();
			parse(onto,out);
			s.add(onto);
			m.remove(onto);
			parseImports(out);
			}
	}

	public static void parseImports(BufferedWriter out)
	{
		Iterator iter = m.entrySet().iterator();
		while(iter.hasNext()) {

			Map.Entry pairs = (Map.Entry)iter.next();
	
			if(checkset(pairs.getValue())) {
				OWLOntology onto = (OWLOntology)pairs.getKey();
				parse(onto,out);
				s.add((OWLOntology)pairs.getKey());
				m.remove(pairs.getKey());
				parseImports(out);
			}
		}
	}

	public static Boolean checkset(Object it)	{
		Set aux = new HashSet();
		aux.add(it);		
		if (s.containsAll(aux))		
			return true;
		else
			return false;
	}

	public static Set getKeysByValue(int value) {
		Set keys = new HashSet();
		Iterator it = m.entrySet().iterator();		
		while(it.hasNext()) {
			Map.Entry pairs = (Map.Entry)it.next();
			if(pairs.getValue().equals(value)) {
				keys.add(pairs.getKey());
			}
		}
     	return keys;
	}
	
	public static void parse(OWLOntology onto, BufferedWriter out)	{
		try {
		ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer (onto.getOWLOntologyManager());
		rendi.render(onto,out);
		} catch(OWLRendererException ex)	{		
			System.err.println("Error by parse!");
			ex.printStackTrace();
		}
	}
}



