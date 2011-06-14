package de.unibremen.informatik.atermRenderer;

import org.semanticweb.owlapi.io.OWLFunctionalSyntaxOntologyFormat;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.OWLRendererIOException;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.io.OWLOntologyDocumentTarget;

import java.io.*;
import java.net.URI;

/**
 * Author: Heng Jiang	<br>
 * The University Of Bremen <br>
 * Date: 10-2007<br><br>
 */

public class OWLATermStorer implements OWLOntologyStorer {

    /**
     * Determines if this storer can store an ontology in the specified ontology format.
     * @param ontologyFormat The desired ontology format.
     * @return <code>true</code> if this storer can store an ontology in the desired
     *         format.
     */
    public boolean canStoreOntology(OWLOntologyFormat ontologyFormat) {
        return ontologyFormat.equals(new OWLATermFormat());
    }


    /**
     * Stores an ontology at the specified physical IRI in the specified format.
     * @param ontology       The ontology to be stored
     * @param physicalIRI    The physical IRI that specifies the location
     * @param ontologyFormat The format that the ontology should be stored in
     */
    public void storeOntology(OWLOntologyManager manager, 
			      OWLOntology ontology, 
			      IRI physicalIRI,
                              OWLOntologyFormat ontologyFormat) throws OWLRendererException {
        try {
            OWLATermRenderer renderer = new OWLATermRenderer(manager);

            File file = new File(physicalIRI.toURI());
            OutputStream os = new FileOutputStream(file);
            renderer.render(ontology, new BufferedWriter(new OutputStreamWriter(os)));
            os.flush();
            os.close();
        }
        catch (IOException e) {
            throw new OWLRendererIOException(e);
        }
    }
 
    public void storeOntology(OWLOntologyManager manager, 
			      OWLOntology ontology, 
			      OWLOntologyDocumentTarget target, 
			      OWLOntologyFormat format) throws OWLOntologyStorageException
    {
    }

    //public void storeOntology(OWLOntologyManager manager, OWLOntology ontology,IRI documentIRI, OWLOntologyFormat ontologyFormat)
	//{
//	}

}
