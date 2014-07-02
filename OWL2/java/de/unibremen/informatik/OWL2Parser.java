import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.coode.owlapi.rdf.rdfxml.RDFXMLRenderer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.StreamDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;
import uk.ac.manchester.cs.owl.owlapi.OWLOntologyIRIMapperImpl;

import java.io.*;
import java.net.*;
import java.util.HashSet;
import java.util.Set;

public class OWL2Parser {
    private static enum OPTION {QUICK_OWL_XML, OWL_XML, MANCHESTER, RDF_XML, OBO}

    private static OPTION op;
    private static Boolean cyclic = false;
    private static final Set<IRI> missingImports = new HashSet<IRI>();
    private static Set<OWLOntology> ontologies;
    private static final Set<OWLOntology> exported = new HashSet<OWLOntology>();
    private static OWLOntologyManager manager = setupManagerWithMissingImportListener();
    private static OWLOntologyIRIMapperImpl mapper = new OWLOntologyIRIMapperImpl();
 
    public static void main(String[] args) {
        // A simple example of how to load and save an ontology
        try {
            op = OPTION.MANCHESTER;
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(System.out));
            switch (args.length) {
                default : 
                    System.out.println("Usage: processor <URI> [FILENAME] <OPTION>");
                    System.exit(1);
                    break;
                // args[0]: IRI
                case 1 :
                    break;
                // args[0]: IRI
                // args[1]: type of output, or otherwise use argument as file name
                // with Manchester syntax
                case 2 :
                    if (!parseOption(args[1]))
                        out = new BufferedWriter(new FileWriter(args[1]));
                    break;
                // args[0]: IRI
                // args[1]: name of output file
                // args[2]: type of output file: xml, rdf, or otherwise assume Manchester syntax
                case 3 :
                    out = new BufferedWriter(new FileWriter(args[1]));
                    parseOption(args[2]);
                    break;
            }
            out.write("<Ontologies>\n");
            /* Load an ontology from a physical IRI */
            String inp = args[0];
            URI uri;
            if (inp.startsWith("http:") || inp.startsWith("https:"))
                uri = new URI(inp);
            else uri = new File(inp).toURI();
            URLConnection con = uri.toURL().openConnection();
            con.addRequestProperty("Accept", "text/plain");
            StreamDocumentSource sds = new StreamDocumentSource(con.getInputStream(), IRI.create(uri));
            OWLOntologyLoaderConfiguration config = new OWLOntologyLoaderConfiguration();
            config = config.setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
            OWLOntology ontology = manager.loadOntologyFromOntologyDocument(sds, config);              
            if (!missingImports.isEmpty()) {
                IRI ontohub = IRI.create("https://ontohub.org/external/");
                for (IRI mi : missingImports) {   
                    mapper.addMapping(mi, ontohub.resolve(mi.toURI().getHost() + mi.toURI().getPath()));
                }
                // reset the manager. clear out imports to avoid duplicates 
                manager = setupManagerWithMissingImportListener();
                manager.addIRIMapper(mapper);
                // collect and report missing imports again.
                missingImports.clear();
                ontology = manager.loadOntologyFromOntologyDocument(sds, config);
                for (IRI mi : missingImports) {
                    out.write("<Missing>" + mi + "</Missing>\n");
                }
            }
            ontologies = getImports(ontology, new HashSet<OWLOntology>());
            if (cyclic) {
                String str = ontology.getOntologyID().getOntologyIRI().toString();
                String merged_name = str + ".merged.owl"; // we must make a new name!
                // System.out.println("NAME: " + merged_name + "\n");
                IRI mergedOntologyIRI = IRI.create(merged_name);
                // System.out.println("MERGED_IRI " + mergedOntologyIRI + "\n");
                OWLOntology merged;
                if (op == OPTION.QUICK_OWL_XML)
                    merged = manager.createOntology(mergedOntologyIRI);
                else {
                    OWLOntologyMerger merger = new OWLOntologyMerger(manager);
                    merged = merger.createMergedOntology(manager, mergedOntologyIRI);
                }
                renderUsingOption(merged, out);
            } else {
                ontologies.add(ontology);
                exportImports(out);
            }
            out.write("\n</Ontologies>\n");
            out.flush();
            out.close();
        } catch (Exception ex) {
            System.err.println("OWL parse error: " + ex.getMessage());
            ex.printStackTrace();
        }
    }

    private static boolean parseOption (String option) {
        if(option.equals("quick")) op = OPTION.QUICK_OWL_XML;
        else if(option.equals("xml")) op = OPTION.OWL_XML;
        else if(option.equals("rdf")) op = OPTION.RDF_XML;
        else if(option.equals("obo")) op = OPTION.OBO;
        else if(option.equals("omn")) op = OPTION.MANCHESTER;
        else return false;
        return true;
    }
        
    private static OWLOntologyManager setupManagerWithMissingImportListener () {
        OWLOntologyManager mgr = OWLManager.createOWLOntologyManager();
        mgr.addMissingImportListener(new HasMissingImports());
        return mgr;
    }

    private static class HasMissingImports implements MissingImportListener {
        @Override
        public void importMissing(MissingImportEvent event) {
            missingImports.add(event.getImportedOntologyURI());
        }
    }

    private static Set<OWLOntology> getImports(OWLOntology ontology, Set<OWLOntology> stop) {
        Set<OWLOntology> s = new HashSet<OWLOntology>();
        Set<OWLOntology> next = new HashSet<OWLOntology>(stop);
        next.add(ontology);
        for (OWLOntology imported : ontology.getDirectImports())
            if (cyclic || next.contains(imported)) cyclic = true;
            else if (!s.contains(imported)) {
                Set<OWLOntology> i = getImports(imported, next);
                s.add(imported);
                s.addAll(i);
            }
        return s;
    }

    private static void exportImports(BufferedWriter out) {
        Boolean changed;
        do {
            changed = false;
            for (OWLOntology onto : ontologies)
                if (exported.containsAll(onto.getDirectImports())) {
                    if (!exported.contains(onto)) {
                        changed = exported.add(onto);
                        renderUsingOption(onto, out);
                    }
                }
        } while (changed);
    }

    private static void renderUsingOption(OWLOntology onto, BufferedWriter out) {
        switch (op) {
            case QUICK_OWL_XML:
                renderAsXml(true, onto, out);
                break;
            case OWL_XML:
                renderAsXml(false, onto, out);
                break;
            case MANCHESTER:
                renderAsOmn(onto, out);
                break;
            case RDF_XML:
                renderAsRdf(onto, out);
                break;
        }
    }

    private static void renderAsOmn(OWLOntology onto, BufferedWriter out) {
        try {
            ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer();
            rendi.render(onto, out);
        } catch (OWLRendererException ex) {
            System.err.println("Error by ManchesterParser!");
            ex.printStackTrace();
        }
    }

    private static void renderAsXml(boolean quick, OWLOntology onto, BufferedWriter out) {
        try {
            OWLXMLRenderer ren = new OWLXMLRenderer();
            File tempFile = File.createTempFile("owlTemp", ".xml");
            FileWriter buf = new FileWriter(tempFile);
            if (quick) {
                onto.getOWLOntologyManager().removeAxioms(onto, onto.getAxioms());
            }
            ren.render(onto, buf);
            buf.flush();
            buf.close();
            BufferedReader rBuf = new BufferedReader(new FileReader(tempFile));
            rBuf.readLine();   // ignore the first line containing <?xml version="1.0"?>
            while (rBuf.ready()) out.append(rBuf.readLine()).append("\n");
            rBuf.close();
            tempFile.deleteOnExit();
            out.append("<Loaded name=\"").append(manager.getOntologyDocumentIRI(onto));
            out.append("\" ontiri=\"").append(onto.getOntologyID().getOntologyIRI()).append("\"/>\n");
        } catch (Exception ex) {
            System.err.println("Error by XMLParser!");
            ex.printStackTrace();
        }
    }

    private static void renderAsRdf(OWLOntology onto, BufferedWriter out) {
        try {
            RDFXMLRenderer rdfrend = new RDFXMLRenderer(onto, out);
            rdfrend.render();
        } catch (IOException ex) {
            System.err.println("Error by RDFParser!");
            ex.printStackTrace();
        }
    }
}
