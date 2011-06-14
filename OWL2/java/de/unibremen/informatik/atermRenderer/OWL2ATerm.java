package de.unibremen.informatik.atermRenderer;

import de.unibremen.informatik.atermRenderer.OWLATermStorer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.IRI;

import aterm.ATerm;
import aterm.ATermList;
import aterm.pure.PureFactory;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URI;
import java.util.ArrayList;

/*
 * Copyright (C) 2007, University of Manchester
 *
 * Modifications to the initial code base are copyright of their
 * respective authors, or their employers as appropriate.  Authorship
 * of the modifications may be determined from the ChangeLog placed at
 * the end of this file.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.

 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.

 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 */

/**
 * <p>
 * Simple example that reads an ontology then writes it out in OWL/XML
 * </p>
 * 
 * Author: Matthew Horridge<br>
 * The University Of Manchester<br>
 * Bio-Health Informatics Group<br>
 * Date: 11-Jan-2007<br>
 * <br>
 */
public class OWL2ATerm {

	private static ArrayList<OWLOntology> loadedImportsList = new ArrayList<OWLOntology>();
	static private ArrayList<IRI> importsIRI = new ArrayList<IRI>();
	
	public static void main(String[] args) {
		PureFactory factory = new PureFactory();
		ATermList ontologyList = factory.makeList();
		ATermFunc af = new ATermFunc();

		if (args.length < 1) {
			System.out.println("Usage: processor <URI> [FILENAME]");
			System.exit(1);
		}

		String filename = "";

		// A simple example of how to load and save an ontology
		try {
			//String aux = args[0].replaceAll("\\<.*?\\>","");
			IRI iri = IRI.create(args[0]);
			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
			manager.addOntologyStorer(new OWLATermStorer());
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
			//System.out.println(iri);
			//IRI physicalIRI = IRI.create(args[0]);
			// Now do the loading
			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(physicalIRI);
			System.out.println(ontology);
			
			// get all ontology which are imported from this ontology.
			getImportsList(ontology, manager);
			//System.out.println(loadedImportsList);	
			//System.out.println("Imports List: " + ImportsList);
			
			//OWLOntologyManager mn = OWLManager.createOWLOntologyManager();
			System.out.println();
			System.out.println("LoadedImportsList: " + loadedImportsList);
			System.out.println();
			int i = 0;
			for (OWLOntology onto : loadedImportsList) {
				//String keyIri = (String) ontos.next();
				//OWLOntology onto = ontos;
				//System.out.println(onto.getOntologyID());
				System.out.println(i + "\n");
				i = i + 1;
				IRI ontoIRI = onto.getOntologyID().getOntologyIRI();
				//System.out.println(ontoIRI);
				System.out.println("parsing OWL: " + ontoIRI + " ...");
				ATerm iriTerm = factory.parse("\"" + ontoIRI + "\"");
				//System.out.println();
				//System.out.println(onto);
				System.out.println("iriTerm is: " + iriTerm);
				ATerm aterm = getATerm(onto, manager);
				
				ontologyList = factory.makeList(factory.makeAppl(af.paarFunc,
						iriTerm, aterm), ontologyList);
			}
			System.out.println("stuck in loop");
			File file = new File(filename);
			ontologyList.reverse().writeToTextFile(new FileOutputStream(file, false));
			String cmd = "cp " + file.getAbsolutePath() + " .outputFilename";
			Runtime.getRuntime().exec(cmd);
			System.out.println("OWL parsing done!\n");
		} catch (IOException e) {
			System.err.println("Error: can not build file: " + filename);
			e.printStackTrace();
		}catch (Exception ex) {
			System.err.println("OWL parse error: " + ex.getMessage());
			ex.printStackTrace();
		}
	}

	static private ATerm getATerm(OWLOntology ontology, OWLOntologyManager manager) {
        try {
            OWLATermRenderer renderer = new OWLATermRenderer(manager);
		//System.out.println("dsds\n");
	    ATerm aaux = renderer.render(ontology);
		//System.out.println("dsds\n");
            return aaux;
        }
        catch (OWLException e) {
          System.err.println("Rendering error" + manager.getOntologyDocumentIRI(ontology));
          e.printStackTrace();
        }
        return null;
    }

	private static void getImportsList(OWLOntology ontology,OWLOntologyManager om) {

		// HashMap hMap = new HashMap();
		ArrayList<OWLOntology> unSavedImports = new ArrayList<OWLOntology>();
		

		if(loadedImportsList.size() == 0)
		{
			loadedImportsList.add(ontology);
			importsIRI.add(om.getOntologyDocumentIRI(ontology));
			//System.out.println(loadedImportsList);
			//System.out.println(importsIRI);
			
		}	
		//System.out.println("err");
		try {
			OWLOntologyManager ma = OWLManager.createOWLOntologyManager();
			for (OWLOntology imported : ontology.getImports()) {
								
				if (!importsIRI.contains(ma.getOntologyDocumentIRI(imported))) {
					unSavedImports.add(imported);
					loadedImportsList.add(imported);
					importsIRI.add(ma.getOntologyDocumentIRI(imported));
				
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
