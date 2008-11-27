package  de.unibremen.informatik.atermRenderer;

import org.semanticweb.owl.io.AbstractOWLRenderer;
import org.semanticweb.owl.io.OWLRendererException;
import org.semanticweb.owl.io.OWLRendererIOException;
// import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLOntology;
import org.semanticweb.owl.model.OWLOntologyManager;

import aterm.ATerm;
import aterm.ATermAppl;

import java.io.IOException;
import java.io.Writer;

/**
 * Author: Heng Jiang <br>
 * The University Of Bremen <br>
 * Date: 10-2007 <br><br>
 */
public class OWLATermRenderer extends AbstractOWLRenderer {

    public OWLATermRenderer(OWLOntologyManager owlOntologyManager) {
        super(owlOntologyManager);
    }

    public ATerm render(OWLOntology ontology) throws OWLException
    {
        OWLATermObjectRenderer ren = new OWLATermObjectRenderer(ontology, getOWLOntologyManager());
        return ren.term(ontology);

    }

    public void render(OWLOntology ontology, Writer writer) throws OWLRendererException {
        try {
            OWLATermObjectRenderer ren = new OWLATermObjectRenderer(ontology, writer, getOWLOntologyManager());
            writer.write(ren.term(ontology).toString());
            // ontology.accept(ren);
            writer.flush();
        }
        catch (IOException e) {
            throw new OWLRendererIOException(e);
        }catch(OWLException e){
        	e.printStackTrace();
        }
    }
}
