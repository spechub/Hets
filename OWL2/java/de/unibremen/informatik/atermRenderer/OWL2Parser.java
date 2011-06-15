//package de.unibremen.informatik.atermRenderer;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.IRI;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URI;
import java.util.ArrayList;


public class OWL2Parser {

	private static ArrayList<OWLOntology> loadedImportsList = new ArrayList<OWLOntology>();
	static private ArrayList<IRI> importsURI = new ArrayList<IRI>();

	public static void main(String[] args) {
		
		if (args.length < 1) {
			System.out.println("Usage: processor <URI> [FILENAME]");
			System.exit(1);
		}

		String filename = "";

		// A simple example of how to load and save an ontology
		try {
			IRI iri = IRI.create(args[0]);
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			if (args.length == 2) {
				filename = args[1];
			} else {
				String[] iriSplit = iri.toURI().getPath().split("/");
				String tmpPath = "/tmp/";
				String pidCmd[] = {
						"/bin/sh",
						"-c",
						"/bin/ps -f | /bin/awk '{print $2,$3}' | /bin/grep \"^$$\" "
								+ "| /bin/awk '{print $2}'" };
				String pidName = "";
				long currTime = 0;
				Process pidProc = Runtime.getRuntime().exec(pidCmd);
				BufferedReader stdout1 = new BufferedReader(
						new InputStreamReader(pidProc.getInputStream()));
				pidName = stdout1.readLine();
				currTime = System.currentTimeMillis();

				String randomName = pidName + "-" + currTime;
				String postfix = ".term";
				filename = tmpPath + iriSplit[iriSplit.length - 1] + "-"
						+ randomName + postfix;
			}
			
			
			/* Load an ontology from a physical IRI */
			IRI physicalIRI = IRI.create(args[0]);
			System.out.println("Loading : " + args[0]);
			
			// Now do the loading
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);
			System.out.println(ontology);
			
			// get all ontology which are imported from this ontology.
			getImportsList(ontology, manager);
			
			//OWLOntologyManager mn = OWLManager.createOWLOntologyManager();
			//System.out.println();
			System.out.println("LoadedImportsList: " + loadedImportsList);
			System.out.println();

			for (OWLOntology onto : loadedImportsList) {
	                             
				System.out.println("parsing OWL: " + onto.getOntologyID().getOntologyIRI() + " ...");
	                               
	                        }

			
	                        File file = new File(filename);
	                       // ontologyList.reverse().writeToTextFile(new FileOutputStream(file, false));
	                        String cmd = "cp " + file.getAbsolutePath() + " .outputFilename";
	                        Runtime.getRuntime().exec(cmd);
	                       // System.out.println("OWL parsing done!\n");
		} catch (IOException e) {
			System.err.println("Error: can not build file: " + filename);
			e.printStackTrace();
		}catch (Exception ex) {
			System.err.println("OWL parse error: " + ex.getMessage());
			ex.printStackTrace();
		}
	}


	private static void getImportsList(OWLOntology ontology,
			OWLOntologyManager om) {

		// HashMap hMap = new HashMap();
		ArrayList<OWLOntology> unSavedImports = new ArrayList<OWLOntology>();
		//System.out.println("ab\n");

		if(loadedImportsList.size() == 0)
		{
			loadedImportsList.add(ontology);
			importsURI.add(om.getOntologyDocumentIRI(ontology));
		}	

		try {
			for (OWLOntology imported : om.getImports(ontology)) {
				if (!importsURI.contains(imported.getOntologyID().getOntologyIRI())) {
					unSavedImports.add(imported);
					loadedImportsList.add(imported);
					importsURI.add(imported.getOntologyID().getOntologyIRI());
				}
			}
			for (OWLOntology onto : unSavedImports) {
				getImportsList(onto, om);
			}

		} catch (Exception e) {
			System.err.println("Error!");
			e.printStackTrace();
		}
	}

}



