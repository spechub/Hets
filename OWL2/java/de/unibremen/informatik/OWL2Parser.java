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
    private static enum OPTION {OWL_XML, MANCHESTER, RDF_XML, OBO, TURTLE, DOL}

    private static OPTION input_type;
    private static OPTION output_type;
    private static Boolean quick = false;
    private static Boolean cyclic = false;
    private static final Set<IRI> missingImports = new HashSet<IRI>();
    private static Set<OWLOntology> ontologies;
    private static final Set<OWLOntology> exported = new HashSet<OWLOntology>();
    private static OWLOntologyManager manager = setupManagerWithMissingImportListener();
    private static OWLOntologyIRIMapperImpl mapper = new OWLOntologyIRIMapperImpl();
    private static String inp = "";
    private static BufferedWriter wrt_out = null;
    
    public static void main(String[] args) {
        // A simple example of how to load and save an ontology
        try {
            if (!parseARGuments(args)) {
                showHelpScreen();
                return;
            }
            wrt_out.write("<Ontologies>\n");
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
                    wrt_out.write("<Missing>" + mi + "</Missing>\n");
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
                // Axioms can be excluded when 'quick' Option selected
                if (quick)
                    merged = manager.createOntology(mergedOntologyIRI);
                else {
                    OWLOntologyMerger merger = new OWLOntologyMerger(manager);
                    merged = merger.createMergedOntology(manager, mergedOntologyIRI);
                }
                renderUsingOption(merged, wrt_out);
            } else {
                ontologies.add(ontology);
                exportImports(wrt_out);
            }
            wrt_out.write("\n</Ontologies>\n");
            wrt_out.flush();
            wrt_out.close();
        } catch (Exception ex) {
            System.err.println("OWL parse error: " + ex.getMessage());
            ex.printStackTrace();
        }
    }

    private static void showHelpScreen()
    {
        String helpText =
           "Usage: processor [<options..>] <URI>\n"
         + "_>_options_<______________\n"
         + " | -o <tp>  ..input type\n"
         + " | -i <tp>  ..output type\n"
         + " - - - tp  <- [owl xml omn rdf obo dol ttl]\n"
         + " | -f <nm>  ..write output file\n"
         + " - - - nm  <- name of output file\n"
         + " | -qk  ..internal(!) sets 'quick' option\n"
         + " | -h  ..this helptext";
        System.out.println( helpText );
    }

    // parse arguments according to option set
    // return false for unknown stuff, or when IRI is not set
    private static Boolean parseARGuments( String[] args )
        throws Exception
    {
        if (args.length == 0) return false;

        input_type = OPTION.MANCHESTER;
        output_type = OPTION.MANCHESTER;
        String tmpFileName = "";
        for (int i = 0; i < args.length; i++) {
            String arg = args[i].toLowerCase();
            if (arg.startsWith("-")) {
                Boolean hasNext = i < args.length-1;
                if (arg.equals("-i") && hasNext) {
                    i += 1;
                    input_type = parseOption(args[i]);
                } else if (arg.equals("-o") && hasNext) {
                    i += 1;
                    output_type = parseOption(args[i]);
                } else if (arg.equals("-f") && hasNext) {
                    i += 1;
                    tmpFileName = args[i];
                } else if (arg.equals("-qk") || arg.equals("-q")) {
                    quick = true;
                } else if (arg.equals("-h") || arg.equals("--help")) {
                    showHelpScreen();
                } else
                    return false;
            } else {
                // TODO: could test here if actually is an IRI
                // .. and test if it's only set once.
                inp = args[i]; // read again to avoid earlier 'toLowerCase'
        }  }
        if (inp.equals("")) return false;
        try {
          if (tmpFileName.equals("")) {
              wrt_out = new BufferedWriter(new OutputStreamWriter(System.out));
          } else wrt_out = new BufferedWriter(new FileWriter(tmpFileName));
        } catch (Exception e) { throw (e); }
        return true;
    }

    private static OPTION parseOption (String opt) {
        opt = opt.toLowerCase();
        if(opt.equals("xml") || opt.equals("owl")) return OPTION.OWL_XML;
        else if(opt.equals("omn")) return OPTION.MANCHESTER;
        else if(opt.equals("rdf")) return OPTION.RDF_XML;
        else if(opt.equals("obo")) return OPTION.OBO;
        else if(opt.equals("dol")) return OPTION.DOL;
        else if(opt.equals("ttl")) return OPTION.TURTLE;
        return OPTION.MANCHESTER; // use omn as default
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

    private static Set<OWLOntology> getImports (OWLOntology ontology, Set<OWLOntology> stop) {
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

    private static void exportImports (BufferedWriter out) {
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

    private static void renderUsingOption (OWLOntology onto, BufferedWriter out) {
        switch (output_type) {
            case OWL_XML :
                renderAsXml(onto, out);
                break;
            case MANCHESTER :
                renderAsOmn(onto, out);
                break;
            case RDF_XML :
                renderAsRdf(onto, out);
                break;
            
            case OBO :
                renderAsXml(onto, out);
                break;
            case DOL :
                renderAsXml(onto, out);
                break;
            case TURTLE :
                renderAsXml(onto, out);
                break;
        }
    }

    private static void renderAsOmn (OWLOntology onto, BufferedWriter out) {
        try {
            ManchesterOWLSyntaxRenderer rendi = new ManchesterOWLSyntaxRenderer();
            rendi.render(onto, out);
        } catch (OWLRendererException ex) {
            System.err.println("Error by ManchesterParser!");
            ex.printStackTrace();
        }
    }

    private static void renderAsXml (OWLOntology onto, BufferedWriter out) {
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

    private static void renderAsRdf (OWLOntology onto, BufferedWriter out) {
        try {
            RDFXMLRenderer rdfrend = new RDFXMLRenderer(onto, out);
            rdfrend.render();
        } catch (IOException ex) {
            System.err.println("Error by RDFParser!");
            ex.printStackTrace();
        }
    }
}
