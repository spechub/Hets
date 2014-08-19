import org.coode.owlapi.owlxml.renderer.OWLXMLRenderer;
import org.coode.owlapi.rdf.rdfxml.RDFXMLRenderer;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.StreamDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.OWLOntologyMerger;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import uk.ac.manchester.cs.owl.owlapi.mansyntaxrenderer.ManchesterOWLSyntaxRenderer;
//import org.coode.owlapi.manchesterowlsyntax.ManchesterOWLSyntaxEditorParser;
//import org.coode.manchesterowlsyntax.ManchesterOWLSyntaxOntologyFormat;
import uk.ac.manchester.cs.owl.owlapi.OWLOntologyIRIMapperImpl;

import java.io.*;
import java.net.*;
import java.util.HashSet;
import java.util.Set;
import java.util.ArrayList;

public class OWL2Parser {
    private static enum OPTION {OWL_XML, MANCHESTER, RDF_XML, OBO, TURTLE, DOL}

    private static Boolean quick = false;
    private static Boolean cyclic = false;
    private static final Set<IRI> missingImports = new HashSet<IRI>();
    private static Set<OWLOntology> ontologies;
    private static final Set<OWLOntology> exported = new HashSet<OWLOntology>();
    private static OWLOntologyManager manager = setupManagerWithMissingImportListener();
    private static OWLOntologyIRIMapperImpl mapper = new OWLOntologyIRIMapperImpl();
    private static URI uri = null;

    public static void main(String[] args) {
        // A simple example of how to load and save an ontology
        try {
            OWLOutputHandler out = new OWLOutputHandler();
            parseArgs (args, out);
            
            out.writeXml("<Ontologies>\n");
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
                    out.writeXml("<Missing>" + mi + "</Missing>\n");
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
                renderUsingOption(merged, out);
            } else {
                ontologies.add(ontology);
                exportImports(out);
            }
            out.writeXml("\n</Ontologies>\n");
            out.flush();
            out.close();
        } catch (Exception ex) {
            System.err.println("OWL parse error: " + ex.getMessage());
            ex.printStackTrace();
        }
    }

    // print usage information screen
    private static void showHelpScreen() {
        System.out.println ("Usage: processor [<options..>] <URI>\n"
         + "_>_options_<______________\n"
         + " | -o <tp> <fn>  ..write output to file\n"
         + " - - - tp  <- type [: owl xml omn rdf obo dol ttl]\n"
         + " - - - fn  <- filename\n"
         + " | -o-sys <tp> ..write output to system.out\n"
         + " - - - - - tp  <- type\n"
         + " | -qk  ..internal(!) sets 'quick' option\n"
         + " | -h  ..this helptext"
    ); }

    // parse arguments according to option set
    // fails for unknown or incomplete arguments, or when IRI is not set
    private static void parseArgs
        (String[] args, OWLOutputHandler out) throws Exception
    {
        String inp = "", msg = "OWL2Parser.parseArgs: ";
        if (args.length == 0)
            throw new Exception (msg + "no arguments provided");
        for (int i = 0; i < args.length; i++) {
            String arg = args[i].toLowerCase();
            if (arg.startsWith("-")) {
                if (arg.equals("-o")){
                    if ( ! (i < args.length-2)) throw new Exception (msg
                      + "insufficient arguments (-o [format] [filename])");
                    out.add (parseOption (args[++i].toLowerCase(), msg), args[++i]);
                } else if (arg.equals("-o-sys")){
                    if ( ! (i < args.length-1)) throw new Exception (msg
                      + "insufficient arguments (-o-sys [format])");
                    out.add (parseOption (args[++i].toLowerCase(), msg));
                } else if (arg.equals("-qk") || arg.equals("-q")) {
                    quick = true;
                } else if (arg.equals("-h") || arg.equals("--help")) {
                    showHelpScreen();
                } else throw new Exception (msg + "unknown command <"+arg+">");
            } else {
                if (!inp.equals(""))
                    throw new Exception (msg + "ambigious IRI");
                inp = args[i]; // read again to undo earlier 'toLowerCase'
                if (arg.startsWith("http:") || arg.startsWith("https:"))
                    uri = new URI(inp);
                else uri = new File(inp).toURI();
        }  }
        if (inp.equals("")) throw new Exception (msg + "IRI not set");
    }

    private static OPTION parseOption (String opt, String err) throws Exception {
        if (opt.equals("xml") || opt.equals("owl")) return OPTION.OWL_XML;
        else if (opt.equals("omn")) return OPTION.MANCHESTER;
        else if (opt.equals("rdf")) return OPTION.RDF_XML;
        else if (opt.equals("obo")) return OPTION.OBO;
        else if (opt.equals("dol")) return OPTION.DOL;
        else if (opt.equals("ttl")) return OPTION.TURTLE;
        throw new Exception (err + "unrecognized owl-format: " + opt);
    }

    // custem OntolgyWriter bundles a BufferedWriter with an OWL output format
    protected static class OWLOntologyWriter extends BufferedWriter {
        protected static OPTION option;

        OWLOntologyWriter (String fn, OPTION op) throws Exception {
                super (new FileWriter (fn));
                option = op;
        }
        OWLOntologyWriter (OPTION op) throws Exception {
            super (new OutputStreamWriter (System.out));
            option = op;
        }
        // conveinience method to avoid xml-tags in other-format output
        void writeXml( String s ) throws Exception {
            if (option == OPTION.OWL_XML) super.write( s );
        }
    }

   // output handler allows and handles a list of output-requests
   protected static class OWLOutputHandler {
        static ArrayList<OWLOntologyWriter> writer
            = new ArrayList<OWLOntologyWriter>();

        void add (OPTION op) throws Exception {
          writer.add (new OWLOntologyWriter (op));
        }
        void add (OPTION op, String filename) throws Exception {
          writer.add (new OWLOntologyWriter (filename, op));
        }
        void writeXml (String s) throws Exception {
            for (OWLOntologyWriter out : writer) {
                out.writeXml (s);
        }   }
        void flush () throws Exception {
            for (OWLOntologyWriter out : writer) {
                out.flush ();
        }   }
        void close () throws Exception {
            for (OWLOntologyWriter out : writer) {
                out.close ();
        }   }
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

    private static void exportImports (OWLOutputHandler out) {
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

    private static void renderUsingOption (OWLOntology onto, OWLOutputHandler outmgr) {
      for (OWLOntologyWriter out : outmgr.writer)
        switch (out.option) {
            case OWL_XML :
                renderAsXml(onto, out);
                break;
            case MANCHESTER :
                renderAsOmn(onto, out);
                break;
            case RDF_XML :
                renderAsRdf(onto, out);
                break;
            // TODO: the below still need implementation!
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
  //          ManchesterOWLSyntaxOntologyFormat omn = new ManchesterOWLSyntaxOntologyFormat();
  //          manager.setOntologyFormat(onto, omn);
  //          manager.saveOntology(onto, omn, out);
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
