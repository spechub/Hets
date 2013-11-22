import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.coode.owlapi.rdf.rdfxml.RDFXMLRenderer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.StreamDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;

import java.io.*;
import java.net.URL;
import java.net.URLConnection;
import java.util.*;

public class OWL2Parser {
    private static enum OPTION {OWL_XML, MANCHESTER, RDF_XML}

    private static OPTION op;
    private static final Set<OWLOntology> loadedImportsList = new HashSet<OWLOntology>();
    private static final Set<IRI> importsIRI = new HashSet<IRI>();
    private static final Map<OWLOntology, List<OWLOntology>> m = new HashMap<OWLOntology, List<OWLOntology>>();
    private static final Set<OWLOntology> expanded = new HashSet<OWLOntology>();

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
            /* Load an ontology from a physical IRI */
            URL physicalUrl = new URL(args[0]);
            URLConnection con = physicalUrl.openConnection();
            con.addRequestProperty("Accept", "text/plain");
            StreamDocumentSource sds = new StreamDocumentSource(con.getInputStream());
            OWLOntologyLoaderConfiguration config = new OWLOntologyLoaderConfiguration();
            config = config.setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            OWLOntology ontology = manager.loadOntologyFromOntologyDocument(sds, config);
            getImportsList(ontology, manager);
            if (loadedImportsList.isEmpty())
                renderUsingOption(ontology, out);
            else {
                IRI ontIri = ontology.getOntologyID().getOntologyIRI();
                if (importsIRI.contains(ontIri)) {
                    importsIRI.remove(ontIri);
                }
                if (loadedImportsList.contains(ontology)) {
                    OWLOntologyMerger merger = new OWLOntologyMerger(manager);
                    String str = ontology.getOntologyID().getOntologyIRI().toString();
                    loadedImportsList.remove(ontology);
                    String merged_name = "";
                    for (OWLOntology aux_ont : loadedImportsList) {
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
                    OWLOntology merged = merger.createMergedOntology(manager, mergedOntologyIRI);
                    renderUsingOption(merged, out);
                } else
                    exportImports(out, ontology);
            }
        } catch (Exception ex) {
            System.err.println("OWL parse error: " + ex.getMessage());
            ex.printStackTrace();
        }
    }

    private static void getImportsList(OWLOntology ontology, OWLOntologyManager om) {
        List<OWLOntology> l = new ArrayList<OWLOntology>();
        try {
            for (OWLOntology imported : om.getDirectImports(ontology)) {
                IRI importIri = imported.getOntologyID().getOntologyIRI();
                if (!importsIRI.contains(importIri)) {
                    loadedImportsList.add(imported);
                    importsIRI.add(importIri);
                    l.add(imported);
                }
            }
            m.put(ontology, l);
            for (OWLOntology onto : l) {
                getImportsList(onto, om);
            }
        } catch (Exception e) {
            System.err.println("Error getImportsList!");
            e.printStackTrace();
        }
    }

    private static void exportImports(BufferedWriter out, OWLOntology ontology) {
        for (Map.Entry<OWLOntology, List<OWLOntology>> pairs : m.entrySet()) {
            List<OWLOntology> values = pairs.getValue();
            OWLOntology onto = pairs.getKey();
            if (checkset(values)) {
                if (!expanded.contains(onto)) {
                    renderUsingOption(onto, out);
                    expanded.add(onto);
                    if (onto != ontology)
                        exportImports(out, ontology);
                }
            }
        }
    }

    private static Boolean checkset(Collection<OWLOntology> it) {
        Boolean noDeps = true;
        for (OWLOntology v : it) if (!expanded.contains(v)) noDeps = false;
        return noDeps;
    }

    private static void renderUsingOption(OWLOntology onto, BufferedWriter out) {
        switch (op) {
            case OWL_XML:
                renderAsXml(onto, out);
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
            ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer(onto.getOWLOntologyManager());
            rendi.render(onto, out);
        } catch (OWLRendererException ex) {
            System.err.println("Error by ManchesterParser!");
            ex.printStackTrace();
        }
    }

    private static void renderAsXml(OWLOntology onto, BufferedWriter out) {
        try {
            OWLOntologyManager mngr = onto.getOWLOntologyManager();
            OWLXMLRenderer ren = new OWLXMLRenderer(mngr);
            ren.render(onto, out);
            out.append("<Loaded name=\"").append(mngr.getOntologyDocumentIRI(onto));
            out.append("\" ontiri=\"").append(onto.getOntologyID().getOntologyIRI()).append("\"/>\n");
        } catch (Exception ex) {
            System.err.println("Error by XMLParser!");
            ex.printStackTrace();
        }
    }

    private static void renderAsRdf(OWLOntology onto, BufferedWriter out) {
        try {
            RDFXMLRenderer rdfrend = new RDFXMLRenderer(onto.getOWLOntologyManager(), onto, out);
            rdfrend.render();
        } catch (IOException ex) {
            System.err.println("Error by RDFParser!");
            ex.printStackTrace();
        }
    }
}
