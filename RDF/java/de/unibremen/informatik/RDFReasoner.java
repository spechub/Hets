import java.io.*;
import com.hp.hpl.jena.rdf.model.*;
import com.hp.hpl.jena.query.*;
import com.hp.hpl.jena.sparql.*;
import com.hp.hpl.jena.update.*;
import java.io.File;
import java.io.BufferedReader;
import java.io.IOException;

public class RDFReasoner extends Object {
	public static void main (String args[]) {

	String current = null;
	
	if (args.length == 0) {
		System.out.println("<rdf_filename> <query_filename>");
		System.exit(1);
	}
	else 
		if (args.length == 1) {
			//System.out.println(current + "\n");
	                String inputFile = null;
	                Model model = ModelFactory.createDefaultModel();
	                try {
	                        inputFile = args[0];
	                        InputStream in = new  FileInputStream(inputFile);
	                        if (in == null) { 
	                                System.out.println("File not found!");
	                                System.exit(1);
	                        } 
	                        else {
	                                current = new File(args[0]).getAbsolutePath();
	                                current = "file://" + current;
	                        }
	                model.read(current);
	                model.write(System.out);
	                } catch(Exception e) {
	                        System.out.println(e.getMessage());
	                        System.exit(1);
	                }
		}
		else {
		//System.out.println(current + "\n");
		String inputQuery = null;
		String inputFile = null;
		String queryString = "";
		Model model = ModelFactory.createDefaultModel();
		try {
			inputFile = args[0];
			inputQuery = args[1];
			BufferedReader query_in = new BufferedReader(new FileReader(inputQuery));
			String line;
			while ((line = query_in.readLine())!=null)
				queryString += line + "\n";

			InputStream in = new  FileInputStream(inputFile);
	  		if (in == null) {  
				System.out.println("File not found!");
				System.exit(1);
			}  
			else {
				current = new File(args[0]).getAbsolutePath();
				current = "file://" + current;
			}
		//System.out.println("\nQuery: " + queryString + "\n");
		model.read(current);
		Query query = QueryFactory.create(queryString);
		
		//Execute query and obtain results
		QueryExecution qe = QueryExecutionFactory.create(query, model);
		ResultSet results = qe.execSelect();
		
		// Output query results	
		ResultSetFormatter.out(System.out, results, query);

		// Important - free up resources used running the query
		qe.close();

		//model.write(System.out);
	 	} catch(Exception e) {
			System.out.println(e.getMessage());
			System.exit(1);
		}
	}
	}	
}
