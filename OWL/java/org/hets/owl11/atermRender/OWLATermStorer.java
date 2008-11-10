package org.hets.owl11.atermRender;

import org.semanticweb.owl.io.OWLFunctionalSyntaxOntologyFormat;
import org.semanticweb.owl.io.OWLRendererException;
import org.semanticweb.owl.io.OWLRendererIOException;
import org.semanticweb.owl.model.*;
import org.semanticweb.owl.io.OWLOntologyOutputTarget;

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
     * Stores an ontology at the specified physical URI in the specified format.
     * @param ontology       The ontology to be stored
     * @param physicalURI    The physical URI that specifies the location
     * @param ontologyFormat The format that the ontology should be stored in
     */
    public void storeOntology(OWLOntologyManager manager, 
			      OWLOntology ontology, 
			      URI physicalURI,
                              OWLOntologyFormat ontologyFormat) throws OWLRendererException {
        try {
            OWLATermRenderer renderer = new OWLATermRenderer(manager);

            File file = new File(physicalURI);
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
			      OWLOntologyOutputTarget target, 
			      OWLOntologyFormat format) throws OWLOntologyStorageException
    {
    }
}
