import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.coode.owlapi.rdf.rdfxml.RDFXMLRenderer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.StreamDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;

import java.io.*;
import java.net.*;
import java.util.HashSet;
import java.util.Set;

public class OWL2Parser {
    private static enum OPTION {QUICK_OWL_XML, OWL_XML, MANCHESTER, RDF_XML}

    private static OPTION op;
    private static Boolean cyclic = false;
    private static Set<OWLOntology> ontologies;
    private static final Set<OWLOntology> exported = new HashSet<OWLOntology>();
    private static final OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

    public static void main(String[] args) {
        if (args.length < 1) {
            System.out.println("Usage: processor <URI> [FILENAME] <OPTION>");
            System.exit(1);
        }
        // A simple example of how to load and save an ontology
        try {
            op = OPTION.MANCHESTER;
            BufferedWriter out = new BufferedWriter(new OutputStreamWriter(System.out));
            if (args.length > 1) {
                // args[0]: IRI
                // args[1]: name of output file
                // args[2]: type of output file: xml, rdf, or otherwise assume Manchester syntax
                String filename = args[1];
                if (args.length == 3) {
                    out = new BufferedWriter(new FileWriter(filename));
                    if (args[2].equals("xml"))
                        op = OPTION.OWL_XML;
                    else if (args[2].equals("quick"))
                        op = OPTION.QUICK_OWL_XML;
                    else if (args[2].equals("rdf"))
                        op = OPTION.RDF_XML;
                } else
                    // args[0]: IRI
                    // args[1]: type of output (or output file for  Manchester syntax)
                    //   xml (OWL XML),
                    //   rdf (RDF/XML),
                    //   or otherwise use argument as file name for Manchester syntax
                    // for xml and rdf output goes to standard output, i.e. System.out
                    if (args[1].equals("xml"))
                        op = OPTION.OWL_XML;
                    else if (args[1].equals("rdf"))
                        op = OPTION.RDF_XML;
                    else
                        out = new BufferedWriter(new FileWriter(filename));
            }
            out.write("<Ontologies>\n");
            /* Load an ontology from a physical IRI */
            String inp = args[0];
            URI uri;
            try {
                uri = new URI(inp);
            } catch (Exception ex) {
                uri = new File(inp).toURI();
            }
            URLConnection con = uri.toURL().openConnection();
            con.addRequestProperty("Accept", "text/plain");
            StreamDocumentSource sds = new StreamDocumentSource(con.getInputStream(), IRI.create(uri));
            OWLOntologyLoaderConfiguration config = new OWLOntologyLoaderConfiguration();
            config = config.setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
            OWLOntology ontology = manager.loadOntologyFromOntologyDocument(sds, config);
            ontologies = getImports(ontology, new HashSet<OWLOntology>());
            if (cyclic) {
                String str = ontology.getOntologyID().getOntologyIRI().toString();
                String merged_name = "";
                for (OWLOntology aux_ont : ontologies) {
                    String mrg = aux_ont.getOntologyID().getOntologyIRI().toString();
                    mrg = mrg.replaceAll("[<>\\(\\) ]", "");
                    mrg = mrg.replaceAll(".*/", "");
                    mrg = mrg.replaceAll("\\[.*]", "");
                    merged_name = merged_name + mrg;
                }
                merged_name = str + merged_name;
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
