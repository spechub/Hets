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
import java.util.*;

@SuppressWarnings("unchecked")
public class OWL2Parser {

	private static ArrayList<OWLOntology> loadedImportsList = new ArrayList<OWLOntology>();
	private static ArrayList<IRI> importsIRI = new ArrayList<IRI>();
	private static Map<OWLOntology,List<OWLOntology>> m = new HashMap<OWLOntology, List<OWLOntology>>(); 
	private static Set<OWLOntology> s = new HashSet<OWLOntology>();
	private static boolean OP;

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
			if (args.length == 3) {
				filename = args[1];
				out = new BufferedWriter(new FileWriter(filename));
				if (args[2].equals("xml"))
					OP = true;
				else
					OP = false;

			} else {
				if (args.length == 2)	{
					if (args[1].equals("xml"))
						OP = true;
					else
						OP = false;
				}
				out = new BufferedWriter(openForFile(null));
			}
						
			/* Load an ontology from a physical IRI */
			IRI physicalIRI = IRI.create(args[0]);
						
			// Now do the loading
			
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);

			getImportsList(ontology, manager);

			if(loadedImportsList.size() == 0)
			{
				if (OP)
					parse2xml(ontology, out, manager);			
				else
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
					if (OP)
						parse2xml(merged, out, manager);	
					else
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

		List<OWLOntology> empty = Collections.emptyList();
		List<OWLOntology> l = new ArrayList<OWLOntology>();
		ArrayList<OWLOntology> unSavedImports = new ArrayList<OWLOntology>();

		try {	
			if (om.getImports(ontology).isEmpty())	{
				m.put(ontology,empty); 
			}
			else 	{ 
			
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

	private static Writer openForFile(String fileName) 
		{ 		
			return new OutputStreamWriter(System.out);
		}
	
	private synchronized static  void parseZeroImports(BufferedWriter out) 
	{
		Set all = getKeysByValue();
		Iterator it = all.iterator();

		while(it.hasNext())	
			{

			OWLOntology onto = (OWLOntology)it.next();
			if (OP)
				parse2xml(onto, out, onto.getOWLOntologyManager());
			else 
				parse(onto,out);
			s.add(onto);
			m.remove(onto);
			parseImports(out);

			}
	}

	
	public synchronized static void parseImports(BufferedWriter out)
	{
		
		Iterator iter = m.entrySet().iterator();
		while((iter.hasNext()) && (!m.isEmpty())) {

			Map.Entry pairs = (Map.Entry)iter.next();
			Set values = new HashSet<OWLOntology>();
			List ls = new ArrayList<OWLOntology>();
			ls.add(pairs.getValue());
			List l = new ArrayList<OWLOntology>();
			l = (List)ls.get(0);
			values = cnvrt(l);

			if(checkset(values)) {

				OWLOntology onto = (OWLOntology)pairs.getKey();		
				if (OP)
					parse2xml(onto, out, onto.getOWLOntologyManager());
				else
					parse(onto,out);
				
			s.add((OWLOntology)pairs.getKey());
			m.remove(iter);
			parseImports(out);
			}				
		}

	}

	public static Set cnvrt(List lst)
	{

		Set st = new HashSet<OWLOntology>();
		Iterator it = lst.iterator();
		
		if (lst.size() == 0)		
			return st;

		while(it.hasNext())
			{
			OWLOntology aux_ont = (OWLOntology)it.next();

			st.add(aux_ont);
			}
		return st;
	}


	public static Boolean checkset(Collection it)	{

		if (it.isEmpty())
			return false;
		Set<OWLOntology> aux = new HashSet<OWLOntology>();
		aux.addAll(it);
		return equalcollections(aux, s);	
	}

	public static Boolean equalcollections(Set l1, Set l2)	{

		Boolean eq = true;

		if(l1.isEmpty() || l2.isEmpty())
			return false;
			
		Iterator itr = l1.iterator();
		if(itr.next().toString().equals("[]"))
			{
			eq = false;		
			}
		
		while (itr.hasNext())
			{
				OWLOntology ont = (OWLOntology)itr.next();	
				if (!l2.contains(ont))
					eq = false;
			}

		Iterator it = l2.iterator();

		if (it.next().toString().equals("[]"))
			{
			eq = false;
			}

		while (it.hasNext())
			{
			OWLOntology on = (OWLOntology)it.next();
			if(!l1.contains(on))
				eq = false;
			}
		
		return eq;
	}


	public static Set getKeysByValue() {
		Set keys = new HashSet();
		Iterator it = m.entrySet().iterator();		
		while(it.hasNext()) {
			Map.Entry pairs = (Map.Entry)it.next();
			if(pairs.getValue().toString().equals("[]")) {
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
	
	public static void parse2xml(OWLOntology onto, BufferedWriter out,OWLOntologyManager mng)	{
		try {
		OWLXMLRenderer ren = new OWLXMLRenderer(mng);
		ren.render(onto,out);
		} catch (OWLRendererException ex)	{
			System.err.println("Error by XMLParser!");
			ex.printStackTrace();
		}
	}
}



