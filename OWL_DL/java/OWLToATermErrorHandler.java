import java.util.ArrayList;
import java.util.List;

import org.semanticweb.owl.io.owl_rdf.OWLRDFErrorHandler;
import org.xml.sax.SAXException;

/*
 * Error Handler
 * 
 * Created on 2005-6-4
 *
 */

/**
 * @author Heng Jiang
 *
 */
public class OWLToATermErrorHandler implements OWLRDFErrorHandler {

	ArrayList list;

	public OWLToATermErrorHandler() {
		list = new ArrayList();
	}

	public void owlFullConstruct(int code, String message) throws SAXException {
	}

	public void owlFullConstruct(int code, String message, Object obj)
			throws SAXException {
	}

	public void error(String message) throws SAXException {
		list.add(message);
		// throw new SAXException();
	}

	public void warning(String message) throws SAXException {
		list.add(message);
	}

	public List getList() {
		return list;
	}

}


