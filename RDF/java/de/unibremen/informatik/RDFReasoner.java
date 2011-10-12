import java.io.*;
import com.hp.hpl.jena.rdf.model.*;
import com.hp.hpl.jena.vocabulary.*;
import java.io.File;
import java.io.IOException;

public class RDFReasoner extends Object {
	public static void main (String args[]) {

	String current = null;
	
	if (args.length == 0) {
		System.out.println("<filename>");
		System.exit(1);
	}
	else {
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
	}	
}
