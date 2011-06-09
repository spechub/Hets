package de.unibremen.informatik.atermRenderer;

import java.util.Map;
import org.coode.xml.OWLOntologyXMLNamespaceManager;

import uk.ac.manchester.cs.owl.owlapi.OWLClassImpl;
import org.semanticweb.owlapi.vocab.OWLXMLVocabulary;
import org.semanticweb.owlapi.vocab.OWLFacet;
import org.semanticweb.owlapi.apibinding.*;
import uk.ac.manchester.cs.owl.owlapi.OWLOntologyImpl;
import static org.semanticweb.owlapi.vocab.OWLXMLVocabulary.*;
import org.semanticweb.owlapi.model.*;
import uk.ac.manchester.cs.owl.owlapi.OWLAnnotationImpl;

import java.io.Writer;
import java.net.URI;
import java.util.*;
import aterm.*;

/**
 * Author: Heng Jiang <br>
 * The University Of Bremen <br>
 * Date: 10-2007 <br><br>
 */

public class OWLATermObjectRenderer implements OWLObjectVisitor {

    private Map<String, String> namespaceMap;
    
    private OWLOntologyXMLNamespaceManager nsm;

    private OWLOntology ontology;

    private Writer writer;

    int lastNewLinePos;

    private boolean writeEntitiesAsIRIs;
    
    private boolean isEntity;
    
    ATermFunc af;
    
    protected ATerm term;
    
	String names[] = { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k",
			"l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x",
			"y", "z" };
	
	// ATermFactory factory = new PureFactory();
    private ATermList declarationsList;
    private ATermList annotationsList;
    private ATermList annotationAxiomsList;
    
    public OWLATermObjectRenderer(OWLOntology ontology, Writer writer, OWLOntologyManager owlOntologyManager) {
        this.ontology = ontology;
        this.writer = writer;
        this.namespaceMap = new HashMap<String, String>();
        writeEntitiesAsIRIs = false;
        isEntity = false;
       // namespaceMap.put(ontology.getURI().toString() + "#", "");
       //  namespaceMap.put(Namespaces.OWL.toString(), "owl");
       // namespaceMap.put(Namespaces.RDFS.toString(), "rdfs");
       // namespaceMap.put(Namespaces.RDF.toString(), "rdf");
       // namespaceMap.put(Namespaces.XSD.toString(), "xsd");
        af = new ATermFunc();
        declarationsList = af.factory.makeList();
        annotationsList = af.factory.makeList();
        annotationAxiomsList = af.factory.makeList();
        nsm = new OWLOntologyXMLNamespaceManager(owlOntologyManager, ontology);
      //  namespaceMap.put(nsm.getDefaultNamespace(), "a");
        for( String prefix : nsm.getPrefixes())
        {
        	if(namespaceMap.containsValue(prefix))
        	{
        		continue;
        	}
        	namespaceMap.put(nsm.getNamespaceForPrefix(prefix), prefix);
        }
    }

    public OWLATermObjectRenderer(OWLOntology ontology, OWLOntologyManager owlOntologyManager) {
        this.ontology = ontology;
        this.namespaceMap = new HashMap<String, String>();
        writeEntitiesAsIRIs = false;
        isEntity = false;
        // namespaceMap.put(ontology.getURI().toString() + "#", "");
        // namespaceMap.put(Namespaces.OWL.toString(), "owl");
        // namespaceMap.put(Namespaces.RDFS.toString(), "rdfs");
        // namespaceMap.put(Namespaces.RDF.toString(), "rdf");
        // namespaceMap.put(Namespaces.XSD.toString(), "xsd");
        af = new ATermFunc();
        declarationsList = af.factory.makeList();
        annotationsList = af.factory.makeList();
        annotationAxiomsList = af.factory.makeList();
        nsm = new OWLOntologyXMLNamespaceManager(owlOntologyManager, ontology);
       // namespaceMap.put(nsm.getDefaultNamespace(), "a");
        for( String prefix : nsm.getPrefixes())
        {
        	if(namespaceMap.containsValue(prefix))
        	{
        		continue;
        	}
        	namespaceMap.put(nsm.getNamespaceForPrefix(prefix), prefix);
        }
    }

    public void addNamespace(String namespace, String prefix) {
        namespaceMap.put(namespace, prefix);
    }

    private String reverseLookUp(IRI iri)
    {
	String baseIRI = iri.getScheme() + ":" +
	    iri.getScheme() +"#";
	String ns = nsm.getPrefixForNamespace(baseIRI);
	String ty = iri.getFragment();
	if (ns == null)
	    {
		return baseIRI + "#" + ty;
	    }
	else
	    {
		return ns + ":" + ty;
	    }
    }

    private ATermAppl renderNamespaces() {
		AFun nsFun1 = af.nsFunc1; 
		AFun nsFun2 =  af.nsFunc2;
		ATermList nsList = af.factory.makeList();
		int index =0;
		
		for (String ns : namespaceMap.keySet()) {
			if(ns.matches("file:/[^/].*")){
				continue;
			}
			ATermAppl nsA = strToATermAppl("<" +ns+ ">");
			String sh = namespaceMap.get(ns);
			if (sh.length() ==0){
				sh = names[index++];
			}
			ATermAppl shrt = strToATermAppl(sh);
			nsList = af.factory.makeList(af.factory.makeAppl(nsFun2, shrt, nsA),nsList);
		}
		return af.factory.makeAppl(nsFun1, nsList.reverse());
    }

    public void visit(OWLAnnotationAxiom axiom) {
        // Done in-line?
    }
    
    private AFun getFuncFromVocabulary(OWLXMLVocabulary v, int number)
    {
    	return af.factory.makeAFun(v.getShortName(), number, false);
    }
    
  //  private AFun getFuncFromVocabulary(OWLDatatypeRestriction v, int number)
//    {
//	// getShortName() - problem
  //  	return af.factory.makeAFun(v.getDatatype(), number, true);
    //}

    private AFun getFuncFromVocabulary(OWLFacet v, int number)
    {
	// getShortName() - problem
    	return af.factory.makeAFun(v.getShortName(), number, true);
    }

    private ATermAppl renderIri(IRI iri) {
    	StringBuffer result = new StringBuffer("");
    	int index = 0;
    	
        for (String ns : namespaceMap.keySet()) {
            if (iri.toString().startsWith(ns)) {
                String iriString = iri.toString();
                String prefix = namespaceMap.get(ns);
                if (prefix.length() > 0) {
                	result.append(prefix + ":");
                }else{
                	result.append(names[index++] + ":");
                }
                return strToATermAppl(result.append(iriString.substring(ns.length(), iriString.length())).toString());
            }
        }
        return strToATermAppl("<" + iri.toString() + ">");
    }

     private ATermAppl renderIri(OWLAnnotationValue val) {
    	StringBuffer result = new StringBuffer("");
    	int index = 0;
    	
        for (String ns : namespaceMap.keySet()) {
            if (val.toString().startsWith(ns)) {
                String iriString = val.toString();
                String prefix = namespaceMap.get(ns);
                if (prefix.length() > 0) {
                	result.append(prefix + ":");
                }else{
                	result.append(names[index++] + ":");
                }
                return strToATermAppl(result.append(iriString.substring(ns.length(), iriString.length())).toString());
            }
        }
        return strToATermAppl("<" + val.toString() + ">");
    }
    
    public void visit(OWLOntology ontology) {
    	try{
    		ATermAppl namespaces = renderNamespaces();
    		ATermAppl onto = renderOWLOntology();
    		term = af.factory.makeAppl(af.ontologyFileFunc, namespaces, onto);
    	}catch(OWLException e)
    	{
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
    		System.err.println("error by ontology" + manager.getOntologyDocumentIRI(ontology));
    		e.printStackTrace();
    	}
    }
    
    private ATermAppl renderOWLOntology() throws OWLException
    {
	OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
    	ATermAppl ontoUri = strToATermAppl("<" + manager.getOntologyDocumentIRI(ontology).toString() + ">");
    	ATermList annoList = af.factory.makeList();
    	ATermList importsList = af.factory.makeList();
    	
	//Ontology annotations are now stored directly in an ontology and not as axioms in an ontology
        for (OWLAnnotation anno : ontology.getAnnotations()) {
        	annoList = af.factory.makeList(term(anno), annoList);
        }
        
        Set<OWLAxiom> axioms = new HashSet<OWLAxiom>(ontology.getAxioms());
        axioms.removeAll(ontology.getImportsDeclarations());
	// NO LONGER AN AXIOM IN OWL 2.0
       // for (OWLImportsDeclaration decl : ontology.getImportsDeclarations()) {
        //	importsList =  af.factory.makeList(term(decl), importsList);
        //}

        ATermList classAxiomList = af.factory.makeList();
        for (OWLClass cls : ontology.getClassesInSignature()) {
        	renderDeclarations(cls);
        	renderAnnotations(cls);
        	ATerm a = term(cls);
            for (OWLAxiom ax : ontology.getAxioms(cls)) {
            	classAxiomList = af.factory.makeList(term(ax), classAxiomList);
            }
        }

        ATermList propAxiomList = af.factory.makeList();
        for (OWLObjectProperty prop : ontology.getObjectPropertiesInSignature()) {
        	renderDeclarations(prop);
        	renderAnnotations(prop);
            for (OWLAxiom ax : ontology.getAxioms(prop)) {
            	propAxiomList = af.factory.makeList(term(ax), propAxiomList);
            }
        }

        for (OWLDataProperty prop : ontology.getDataPropertiesInSignature()) {
        	renderDeclarations(prop);
        	renderAnnotations(prop);
            for (OWLAxiom ax : ontology.getAxioms(prop)) {
            	propAxiomList = af.factory.makeList(term(ax), propAxiomList);;
            }
        }


        ATermList individualList = af.factory.makeList();
        for (OWLNamedIndividual ind : ontology.getIndividualsInSignature()) {
        	renderDeclarations(ind);
        	renderAnnotations(ind);
            for (OWLAxiom ax : ontology.getAxioms(ind)) {
            	individualList = af.factory.makeList(term(ax), individualList);;
            }
        }

        for (OWLClassAxiom ax : ontology.getGeneralClassAxioms()) {
        	classAxiomList = af.factory.makeList(term(ax), classAxiomList);
        }

      /*  for (OWLSubPropertyChainOfAxiom ax : ontology.getPropertyChain()) {
            propAxiomList = af.factory.makeList(term(ax), propAxiomList);
        }*/
        return af.factory.makeAppl(af.ontologyFunc, ontoUri, importsList, annoList, declarationsList.concat(classAxiomList.reverse().concat(propAxiomList.reverse().concat(individualList.reverse().concat(annotationAxiomsList)))));
    }

    private void renderAnnotations(OWLEntity entity) throws OWLException
    {
    	annotationsList = af.factory.makeList();
        for (OWLAnnotation ax : entity.getAnnotations(ontology)) {
            annotationsList = af.factory.makeList(term(ax), annotationsList);
        }
        for(OWLAnnotationAxiom ax : entity.getAnnotationAssertionAxioms(ontology)){
        	annotationAxiomsList = af.factory.makeList(term(ax), annotationAxiomsList);
        }
    }
    
    private void renderDeclarations(OWLEntity entity) throws OWLException
    {
        for (OWLAxiom ax : ontology.getDeclarationAxioms(entity)) {
            declarationsList = af.factory.makeList(term(ax), declarationsList);
        }
    }
    
    private ATermAppl render(OWLXMLVocabulary v, OWLObject o) throws OWLException
    {
    	return af.factory.makeAppl(getFuncFromVocabulary(v, 1), term(o));
    }

    private ATermList renderObjects(Collection<? extends OWLObject> objects) throws OWLException
    {
    	ATermList list = af.factory.makeList();
    	for(Iterator<? extends OWLObject> it = objects.iterator(); it.hasNext();){
    		list = af.factory.makeList(term(it.next()), list);
    	}
    	return list.reverse();
    }

    private ATermList renderAnnotations(OWLAxiom ax) throws OWLException
    {
    	ATermList annoAxioms = renderObjects(ontology.getAxioms());
											   	
        for (OWLAnnotation annoAx : ax.getAnnotations()) {
            annoAxioms = af.factory.makeList(term(annoAx), annoAxioms);
        }
        return annotationsList.concat(annoAxioms.reverse());
    }


    public void visit(OWLAnnotationImpl annotation) {
    	try{
    		ATerm annoValue = term(annotation.getValue());

        if (annotation.isLabel()) {
            term = af.factory.makeAppl(af.labelAnnoFunc, annoValue);
        }
        else if (annotation.isComment()) {
            term = af.factory.makeAppl(af.commAnnoFunc, annoValue);
        }
        else {
        	ATermAppl annoIri = renderIri(annotation.getValue()); 
        	term = af.factory.makeAppl(af. explicitAnnoFunc, annoIri, annoValue);
        }    	
        }catch(OWLException e)
    	{
    		System.err.println("error by make term of annotation value: " + annotation);
    		e.printStackTrace();
    	}
    }


/*    public void visit(OWLAnnotationObject annotation) {
    	try{
    		this.writeEntitiesAsIRIs = true;
    		ATerm annoValue = term(annotation);
    		this.writeEntitiesAsIRIs = false;
    	   	annoVV = af.factory.makeAppl(af.UntypedConstantFunc, annoValue);
        	ATermAppl annoIri = renderIri(annotation.getValue());
    		term = af.factory.makeAppl(af. explicitAnnoFunc, annoIri, annoVV);
    	}catch(OWLException e)
    	{
    		System.err.println("error by make term of annotation value: " + annotation);
    		e.printStackTrace();
    	}
    }
*/
    public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.antiSymObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by Asymmetric object property: " + axiom);
    		e.printStackTrace();
    	}
    }


//    public void visit(OWLAnnotationAxiom axiom) {
    	// done inline
  //}
    public void visit(OWLDatatypeDefinitionAxiom axiom)
	{
	}

    public void visit(OWLHasKeyAxiom axiom)
	{
	}	 

    public void visit(OWLSubDataPropertyOfAxiom prop)
	{
	}
    public void visit(OWLAnnotationPropertyRangeAxiom ax)
	{
	}

      public void visit(OWLAnnotationPropertyDomainAxiom ax)
	{
	} 	

      public void visit(OWLSubAnnotationPropertyOfAxiom ax)
	{
	}

      public void visit(OWLAnnotationAssertionAxiom ax)
	{
	}

      public void visit(OWLDataHasValue ax)
	{
	}

      public void visit(OWLDataAllValuesFrom val)
	{
	}

      public void visit(OWLLiteral lit)
	{
	}

      public void visit(OWLDataUnionOf data)
	{
	}

      public void visit(OWLDataIntersectionOf dat)
	{
	}

      public void visit(OWLAnnotationProperty pro)
	{
	}

      public void visit(OWLAnonymousIndividual an)
	{
	}

      public void visit(IRI ir)
	{
	}

      public void visit(OWLAnnotation an)
	{
	}

      public void visit(SWRLLiteralArgument arg)
	{
	}

    public void visit(OWLClassAssertionAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm des = term(axiom.getClassExpression());
    		this.writeEntitiesAsIRIs = true;
    		ATerm ind = term(axiom.getIndividual());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.classAssertionFunc, annoOfAxiom, ind, des);
    	}catch(OWLException e){
    		System.err.println("error by class assersion axiom: " + axiom);
    		e.printStackTrace();
    	}
    }

    public void visit(OWLDataPropertyAssertionAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm prop = term(axiom.getProperty());
    		ATerm sub = term(axiom.getSubject());
    		ATerm obj = term(axiom.getObject());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.dataPropAssertionFunc, annoOfAxiom, prop, sub, obj);
    	}catch(OWLException e){
    		System.err.println("error by data property assersion axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataPropertyDomainAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm prop = term(axiom.getProperty());
    		this.writeEntitiesAsIRIs =false;
    		ATerm domain = term(axiom.getDomain());
    		term =  af.factory.makeAppl(af.dataPropDomainFunc, annoOfAxiom, prop, domain);
    	}catch(OWLException e){
    		System.err.println("error by data property domain axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataPropertyRangeAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm prop = term(axiom.getProperty());
    		this.writeEntitiesAsIRIs = false;
    		ATerm range = term(axiom.getRange());

    		term =  af.factory.makeAppl(af.dataPropRangeFunc, annoOfAxiom, prop, range);
    	}catch(OWLException e){
    		System.err.println("error by data property range axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLSubPropertyAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm sub = term(axiom.getSubProperty());
    		ATerm sup = term(axiom.getSuperProperty());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.subDataPropFunc, annoOfAxiom, sub, sup);
    	}catch(OWLException e){
    		System.err.println("error by sub data property axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDeclarationAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm entity = term(axiom.getEntity());
    		term =  af.factory.makeAppl(af.declFunc, annoOfAxiom, entity);
    	}catch(OWLException e){
    		System.err.println("error by declaration: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDifferentIndividualsAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATermList individuels = renderObjects(axiom.getIndividuals());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.diffIndividualsFunc, annoOfAxiom, individuels);
    	}catch(OWLException e){
    		System.err.println("error by defferent individuals: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDisjointClassesAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATermList desc = renderObjects(axiom.getNestedClassExpressions());
    		term =  af.factory.makeAppl(af.disjointClassFunc, annoOfAxiom, desc);
    	}catch(OWLException e){
    		System.err.println("error by disjoint classes: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDisjointDataPropertiesAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATermList props = renderObjects(axiom.getProperties());
    		term =  af.factory.makeAppl(af.disjointDataPropFunc, annoOfAxiom, props);
    	}catch(OWLException e){
    		System.err.println("error by disjoint data properties: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATermList props = renderObjects(axiom.getProperties());
    		term =  af.factory.makeAppl(af.disjointObjPropFunc, annoOfAxiom, props);
    	}catch(OWLException e){
    		System.err.println("error by disjoint object properties: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDisjointUnionAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm clazz = term(axiom.getOWLClass());
    		this.writeEntitiesAsIRIs = false;
    		ATermList desc = renderObjects(axiom.getClassExpressions());
    		term =  af.factory.makeAppl(af.disjointUnionFunc, annoOfAxiom, clazz, desc);
    	}catch(OWLException e){
    		System.err.println("error by disjoint union: " + axiom);
    		e.printStackTrace();
    	}
    }

       public void visit(OWLEquivalentClassesAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom); 
    		Set<OWLClassExpression> equivSet = axiom.getNestedClassExpressions();
    		ATermList list;
    		list = renderObjects(equivSet);
    		term =  af.factory.makeAppl(af.eqClassFunc, annoOfAxiom, list); 
    	}catch(OWLException e){
    		System.err.println("error by equivalent classes: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATermList prop = renderObjects(axiom.getProperties());
       		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.eqDataPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by equivalent data properties: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATermList prop = renderObjects(axiom.getProperties());
    		term =  af.factory.makeAppl(af.eqObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by equivalent object properties: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLFunctionalDataPropertyAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm prop = term(axiom.getProperty());
    		this.writeEntitiesAsIRIs =false;
    		term = af.factory.makeAppl(af.funcDataPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by functional data property: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.funcObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by functional object property: " + axiom);
    		e.printStackTrace();
    	}
    }

// No longer an axiom on OWL 2.0
//    public void visit(OWLImportsDeclaration axiom) {
    		// ATermList annoOfAxiom = renderAnnotations(axiom);
    		// ATermAppl uri = 
//    		term = renderIri(axiom.getImportedOntologyURI());;
//    }


    public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.invFuncObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by inverse functional object property: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLInverseObjectPropertiesAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm fst = term(axiom.getFirstProperty());
    		ATerm snd = term(axiom.getSecondProperty());
    		term =  af.factory.makeAppl(af.invObjPropFunc, annoOfAxiom, fst, snd);
    	}catch(OWLException e){
    		System.err.println("error by inverse object properties axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.irrefFuncObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by irrefelexive functional object property: " + axiom);
    		e.printStackTrace();
    	}
   }


    public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
    	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATerm prop = term(axiom.getProperty());
    		ATerm sub = term(axiom.getSubject());
    		ATerm obj = term(axiom.getObject());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.negDataPropAssertionFunc, annoOfAxiom, prop, sub,obj);
    	}catch(OWLException e){
    		System.err.println("error by negative data property assertion axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		ATerm sub = term(axiom.getSubject());
    		ATerm obj = term(axiom.getObject());
    		term =  af.factory.makeAppl(af.negObjPropAssertionFunc, annoOfAxiom, prop, sub,obj);
    	}catch(OWLException e){
    		System.err.println("error by negative object property assertion axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectPropertyAssertionAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		this.writeEntitiesAsIRIs = true;
    		ATerm sub = term(axiom.getSubject());
    		ATerm obj = term(axiom.getObject());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.objPropAssertionFunc, annoOfAxiom, prop, sub,obj);
    	}catch(OWLException e){
    		System.err.println("error by object property assertion axiom: " + axiom);
    		e.printStackTrace();
    	}
    }

    public void visit(OWLSubPropertyChainOfAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATermList propChain = renderObjects(axiom.getPropertyChain());
    		ATerm sup = term(axiom.getSuperProperty());
    		ATermAppl chain = af.factory.makeAppl(af.subObjPropChainFunc, propChain);
    		term =  af.factory.makeAppl(af.subObjPropOfFunc, annoOfAxiom, chain, sup);
    	}catch(OWLException e){
    		System.err.println("error by object property chain sub property axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectPropertyDomainAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		ATerm domain = term(axiom.getDomain());
    		term =  af.factory.makeAppl(af.objPropDomainFunc, annoOfAxiom, prop ,domain);
    	}catch(OWLException e){
    		System.err.println("error by object property domain axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectPropertyRangeAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		ATerm range = term(axiom.getRange());
    		term =  af.factory.makeAppl(af.objPropRangeFunc, annoOfAxiom, prop ,range);
    	}catch(OWLException e){
    		System.err.println("error by object property range axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLSubObjectPropertyOfAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm sub = term(axiom.getSubProperty());
    		ATerm sup = term(axiom.getSuperProperty());
    		term =  af.factory.makeAppl(af.subObjPropOfFunc, annoOfAxiom, af.factory.makeAppl(af.objPropExpressionFunc, sub), sup);
    	}catch(OWLException e){
    		System.err.println("error by sub object property  axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
      	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.refObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by refelexive functional object property: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLSameIndividualAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		this.writeEntitiesAsIRIs = true;
    		ATermList ind = renderObjects(axiom.getIndividuals());
    		this.writeEntitiesAsIRIs = false;
    		term =  af.factory.makeAppl(af.sameIndFunc, annoOfAxiom, ind);
    	}catch(OWLException e){
    		System.err.println("error by same individuals axiom: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLSubClassOfAxiom axiom) {
       	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm sub = term(axiom.getSubClass());
    		ATerm sup = term(axiom.getSuperClass());
    		term =  af.factory.makeAppl(af.subClassOfFunc, annoOfAxiom, sub, sup);
    	}catch(OWLException e){
    		System.err.println("error by sub class of  axiom: " + axiom);
    		e.printStackTrace();
    	}
    }

    public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
      	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.symObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by symmetric object property: " + axiom);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
      	try{
    		ATermList annoOfAxiom = renderAnnotations(axiom);
    		ATerm prop = term(axiom.getProperty());
    		term = af.factory.makeAppl(af.transObjPropFunc, annoOfAxiom, prop);
    	}catch(OWLException e){
    		System.err.println("error by symmetric object property: " + axiom);
    		e.printStackTrace();
    	}
    }

    public void visit(OWLClass desc) {
    	if(!writeEntitiesAsIRIs) {
    		if(!isEntity) term = af.factory.makeAppl(af.classFunc, renderIri(desc.getIRI()));
    		else term = af.factory.makeAppl(af.entityClassFunc, renderIri(desc.getIRI()));
    	}else{
    		term = renderIri(desc.getIRI());
    	}
    }
    
    private ATermAppl renderRestriction(OWLXMLVocabulary v, OWLCardinalityRestriction restriction)  throws OWLException{
    	AFun func = af.factory.makeAFun(v.getShortName(), 3, false);
    	ATermInt cardinality =   af.factory.makeInt(restriction.getCardinality());
    	if(restriction.getProperty() instanceof OWLDataPropertyExpression){
    		this.writeEntitiesAsIRIs = true;
    	}
    	ATerm prop = term(restriction.getProperty());
    	this.writeEntitiesAsIRIs = false;
    	ATerm maybeQualified;
    	if(restriction.isQualified()){
    		maybeQualified = af.factory.makeAppl(af.justFunc, term(restriction.getFiller()));
    	}else{
    		maybeQualified = af.factory.makeAppl(af.nothingFunc);
    	}
    	return af.factory.makeAppl(func, cardinality, prop, maybeQualified);
    }

    private ATermAppl renderRestriction(OWLXMLVocabulary v, OWLQuantifiedRestriction restriction)  throws OWLException{
        return renderRestriction(v, restriction.getProperty(), restriction.getFiller());
    }

    private ATermAppl renderRestriction(OWLXMLVocabulary v, OWLPropertyExpression propE, OWLObject filler)  throws OWLException{
    	AFun func = af.factory.makeAFun(v.getShortName(), 2, false);
    	ATerm prop = term(propE);
    	ATerm maybeQualified;
    	if(filler instanceof OWLIndividual)   this.writeEntitiesAsIRIs = true;
    	maybeQualified = term(filler);
    	this.writeEntitiesAsIRIs = false;
    	return af.factory.makeAppl(func, prop, maybeQualified);
    }

    public void visit(OWLQuantifiedDataRestriction desc) {
    	try{ 
    		term  = renderRestriction(DATA_ALL_VALUES_FROM, desc, new ArrayList ());
    	}catch(OWLException e){
    		System.err.println("error by data all restriction: " + desc);
    		e.printStackTrace();
    	}
    }

    private  ATermAppl renderRestriction(OWLXMLVocabulary v, OWLQuantifiedRestriction restriction, List l)  throws OWLException{
        // return renderRestriction(v, restriction.getProperty(), restriction.getFiller());
    	AFun func = af.factory.makeAFun(v.getShortName(), 3, false);
    	this.writeEntitiesAsIRIs = true;
    	ATerm prop = term(restriction.getProperty());
    	this.writeEntitiesAsIRIs = false;
    	ATermList propertyList = af.factory.makeList();
    	OWLObject filler = restriction.getFiller();
    	ATerm maybeQualified;
    	if(filler instanceof OWLIndividual)   this.writeEntitiesAsIRIs = true;
    	maybeQualified = term(filler);
    	this.writeEntitiesAsIRIs = false;
    	return af.factory.makeAppl(func, prop, propertyList, maybeQualified);
    }

    public void visit(OWLDataExactCardinality desc) {
    	try{
    		term = renderRestriction(DATA_EXACT_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data exact cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataMaxCardinality desc) {
    	try{
    		term = renderRestriction(DATA_MAX_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data max  cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataMinCardinality desc) {
    	try{
    		term = renderRestriction(DATA_MIN_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data min  cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataSomeValuesFrom desc) {
    	try{
    		term = renderRestriction(DATA_SOME_VALUES_FROM, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data some restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLHasValueRestriction desc) {
    	try{
    		term = renderRestriction(DATA_HAS_VALUE, desc.getProperty(), desc.getValue());
        	AFun func = af.factory.makeAFun(DATA_HAS_VALUE.getShortName(), 2, false);
        	this.writeEntitiesAsIRIs = true;
        	ATerm prop = term(desc.getProperty());
        	ATerm maybeQualified;
        	// if(filler instanceof OWLIndividual)   this.writeEntitiesAsIRIs = true;
        	maybeQualified = term(desc.getValue());
        	this.writeEntitiesAsIRIs = false;
        	term =  af.factory.makeAppl(func, prop, maybeQualified);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data value restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectAllValuesFrom desc) {
    	try{
    		term = renderRestriction(OBJECT_ALL_VALUES_FROM, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object all  restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectComplementOf desc) {
    	try{
    		term = render(OBJECT_COMPLEMENT_OF, desc.getOperand());
    	}catch(OWLException e)
    	{
    		System.err.println("error by object complement of: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectExactCardinality desc) {
    	try{
    		term = renderRestriction(OBJECT_EXACT_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object exact cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectIntersectionOf desc) {
    	try{
    		AFun func = getFuncFromVocabulary(OBJECT_INTERSECTION_OF, 1);
    		ATermList operands = renderObjects(desc.getOperands());
    		term = af.factory.makeAppl(func, operands);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object intersection of: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectMaxCardinality desc) {
    	try{
    		term = renderRestriction(OBJECT_MAX_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object max cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectMinCardinality desc) {
    	try{
    		term = renderRestriction(OBJECT_MIN_CARDINALITY, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object min cardinality restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectOneOf desc) {
    	try{
    		AFun func = getFuncFromVocabulary(OBJECT_ONE_OF, 1);
    		this.writeEntitiesAsIRIs = true;
    		ATermList ind = renderObjects(desc.getIndividuals());
    		this.writeEntitiesAsIRIs = false;
    		term = af.factory.makeAppl(func, ind);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object one of restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectHasSelf desc) {
    	try{
    		AFun func = getFuncFromVocabulary(OBJECT_HAS_SELF, 1);
    		ATerm  prop = term(desc.getProperty());
    		term = af.factory.makeAppl(func, prop);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object self restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectSomeValuesFrom desc) {
    	try{
    		term = renderRestriction(OBJECT_SOME_VALUES_FROM, desc);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object some value restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectUnionOf desc) {
       	try{
    		AFun func = getFuncFromVocabulary(OBJECT_UNION_OF, 1);
    		ATermList  operands = renderObjects(desc.getOperands());
    		term = af.factory.makeAppl(func, operands);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object union of: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLObjectHasValue desc) {
    	try{
    		term = renderRestriction(OBJECT_HAS_VALUE, desc.getProperty(), desc.getValue());
    	}catch(OWLException e)
    	{
    		System.err.println("error by object  has value restriction: " + desc);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataComplementOf node) {
    	try{
    		AFun func = getFuncFromVocabulary(DATA_COMPLEMENT_OF, 1);
    		ATerm  prop = term(node.getDataRange());
    		term = af.factory.makeAppl(func, prop);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object self restriction: " + node);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDataOneOf node) {
       	try{
    		AFun func = getFuncFromVocabulary(DATA_ONE_OF, 1);
    		ATermList  values = renderObjects(node.getValues());
    		term = af.factory.makeAppl(func, values);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data one of: " + node);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLDatatype node) {
    		term = af.factory.makeAppl(af.dataTypeFunc, renderIri(node.getIRI()));
    }


    public void visit(OWLDatatypeRestriction node) {
    	try{
    		AFun func = getFuncFromVocabulary(DATATYPE_RESTRICTION, 2);
    		AFun nullFunc = af.factory.makeAFun("", 2, false);
    		ATerm dataRange = term(node.getDatatype());
    		ATermList resList =af.factory.makeList();
            for (OWLFacetRestriction restriction : node.getFacetRestrictions()) {
            	ATerm facet = af.factory.parse( restriction.getFacet().getShortName().toUpperCase() );
            	ATerm value = term(restriction.getFacetValue());
            	ATerm dtr = af.factory.makeAppl(nullFunc, facet, value);
            	resList = af.factory.makeList(dtr, resList);
            }
            term = af.factory.makeAppl(func, dataRange, resList.reverse());
    	}catch(OWLException e)
    	{
    		System.err.println("error by data range restriction: " + node);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLFacetRestriction node) {
    	try{
    		AFun func = getFuncFromVocabulary(node.getFacet(), 1);
    		ATerm value = term(node.getFacetValue());
    		term = af.factory.makeAppl(func, value);
    	}catch(OWLException e)
    	{
    		System.err.println("error by data range facet restriction: " + node);
    		e.printStackTrace();
    	}
    }

   /* public void visit(OWLTypedConstant node) {
	String lit = modSpecialCodes(node.getLiteral());
	URI uri = node.getDatatype().getURI();
	String pa = this.reverseLookUp(uri);
	term = af.factory.makeAppl(af.typedConstantFunc, af.factory.parse("\"" + lit + "^^" + pa + "\""));
    }
*/
    private String modSpecialCodes(String literal) {
		StringBuffer lit = new StringBuffer(literal);
		StringBuffer sb = new StringBuffer();
		for(int i = 0; i < lit.length(); i++){
			switch(lit.charAt(i)){
			case '\"' : sb.append("&quot;");  break;
			case '<' :  sb.append("&lt;");  break;
			case '>' : sb.append("&gt;");  break;
			default:   sb.append(lit.charAt(i));
			}
		}
		return sb.toString();
	}

/*	public void visit(OWLUntypedConstant node) {
    	String lang = "";
    	if(node.hasLang()){
    		lang = "@" + node.getLang();
    	}
		String cons = modSpecialCodes(node.getLiteral()) +  lang;
		term = af.factory.makeAppl(af.UntypedConstantFunc, af.factory.parse("\"" + cons + "\""));
    }
*/

    public void visit(OWLDataProperty property) {
    	AFun func = this.getFuncFromVocabulary(DATA_PROPERTY, 1);
        if (!writeEntitiesAsIRIs) {
        	term = af.factory.makeAppl(func, renderIri(property.getIRI()));
        }else{
        	term = renderIri(property.getIRI());
        }
    }


    public void visit(OWLObjectProperty property) {
    	AFun func = af.factory.makeAFun("OpURI", 1, false); 
        if (!writeEntitiesAsIRIs) {
        	if(isEntity){
        		term = af.factory.makeAppl(af.factory.makeAFun("ObjectProperty", 1, false), renderIri(property.getIRI()));
        	}	else {
        		term = af.factory.makeAppl(func, renderIri(property.getIRI()));
        	}
        }else{
        	term = renderIri(property.getIRI());
        }
    	/*
    	AFun func = this.getFuncFromVocabulary(OBJECT_PROPERTY, 1); 
        if (!writeEnitiesAsURIs) {
        	term = af.factory.makeAppl(func, renderIri(property.getIRI()));
        }else{
        	term = renderIri(property.getIRI());
        }*/
    }


    public void visit(OWLObjectInverseOf property) {
       	try{
    		// AFun func = getFuncFromVocabulary(INVERSE_OBJECT_PROPERTY, 1);
       		AFun func = af.factory.makeAFun("InverseOp", 1, false);
    		ATerm  values = term(property.getInverse());
    		term = af.factory.makeAppl(func, values);
    	}catch(OWLException e)
    	{
    		System.err.println("error by object property inverse: " + property);
    		e.printStackTrace();
    	}
    }


    public void visit(OWLNamedIndividual individual) {
    	AFun func = this.getFuncFromVocabulary(NAMED_INDIVIDUAL, 1);
        if (!writeEntitiesAsIRIs || isEntity) {
        	term = af.factory.makeAppl(func, renderIri(individual.getIRI()));
        }else{
        	term = renderIri(individual.getIRI());
        }
    }


    public void visit(SWRLRule rule) {
    }


    public void visit(SWRLDifferentIndividualsAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLClassAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLDataPropertyAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLObjectPropertyAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLDataRangeAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLBuiltInAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLVariable node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLUnaryAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLIndividualArgument node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }


    public void visit(SWRLSameIndividualAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }
/*

    public void visit(SWRLSameAsAtom node) {
        throw new RuntimeException("NOT IMPLEMENTED!");
    }
*/    
	private ATermAppl strToATermAppl(String str) {
		return af.factory.makeAppl(af.factory.makeAFun(str, 0, true));
	}
	
	public ATerm term(OWLObject d) throws OWLException {
        reset();
		d.accept(this);
		ATerm a = result();
		if(a == null) {
			throw new OWLOntologyStorageException("Cannot create ATerm from description " + d);
		}
		return a;		
	}
	
	private void reset()
	{
		this.term = null;
	}
	
	private ATerm result()
	{
		return this.term;
	}
}
