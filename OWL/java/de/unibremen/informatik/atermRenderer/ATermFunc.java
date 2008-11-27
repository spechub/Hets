package de.unibremen.informatik.atermRenderer;

import org.semanticweb.owl.vocab.OWLXMLVocabulary;

import aterm.*;
import aterm.pure.*;
import static org.semanticweb.owl.vocab.OWLXMLVocabulary.*;

public class ATermFunc {

	public ATermFunc() {}
	
		ATermFactory factory = new PureFactory();
		
		AFun ontologyFileFunc = factory.makeAFun("OntologyFile", 2, false);
		AFun ontologyFunc = factory.makeAFun("Ontology", 4, false);
		ATermList ontologyList = factory.makeList();
		
		AFun warnFunc = factory.makeAFun("ParseWarning", 1, false);
		AFun errFunc = factory.makeAFun("ParseError", 1, false);
		AFun paarFunc = factory.makeAFun("UOPaar", 2, false);
		AFun axFunc = factory.makeAFun("Ax", 1, false);
		AFun ontologyPropertyFunc = factory.makeAFun("OntologyProperty", 2, false);
		AFun uriAnnoFunc = factory.makeAFun("URIAnnotation", 2, false);
		AFun messageFunc = factory.makeAFun("MassageList", 1, false);

		AFun fcFunc = factory.makeAFun("Fc", 1, false);
		AFun annoFunc = factory.makeAFun("Anno", 1, false);
		AFun superFunc = factory.makeAFun("Super", 1, false);
		AFun justFunc = factory.makeAFun("J", 1, false);
		AFun nothingFunc = factory.makeAFun("N", 0, false);

		
		AFun nsFunc1 = factory.makeAFun("Namespace", 1, false);
		AFun nsFunc2 = factory.makeAFun("NS", 2, false);
		
		AFun labelAnnoFunc = factory.makeAFun(LABEL.getShortName(), 1, false);
		AFun commAnnoFunc =  factory.makeAFun(COMMENT.getShortName(), 1, false);
		AFun explicitAnnoFunc =  factory.makeAFun("ExplicitAnnotation", 2, false);
		
		AFun antiSymObjPropFunc = factory.makeAFun(ANTI_SYMMETRIC_OBJECT_PROPERTY.getShortName(), 2, false);
		AFun classAssertionFunc = factory.makeAFun(CLASS_ASSERTION.getShortName(), 3, false);
		AFun dataPropAssertionFunc = factory.makeAFun(DATA_PROPERTY_ASSERTION.getShortName(), 4, false);
		AFun dataPropDomainFunc = factory.makeAFun(DATA_PROPERTY_DOMAIN.getShortName(), 3, false);
		AFun dataPropRangeFunc = factory.makeAFun(DATA_PROPERTY_RANGE.getShortName(), 3, false);
		AFun subDataPropFunc = factory.makeAFun(SUB_DATA_PROPERTY_OF.getShortName(), 3, false);
		AFun declFunc = factory.makeAFun(DECLARATION.getShortName(), 2, false);
		AFun diffIndividualsFunc = factory.makeAFun(DIFFERENT_INDIVIDUALS.getShortName(), 2, false);	
		AFun disjointClassFunc = factory.makeAFun(DISJOINT_CLASSES.getShortName(), 2, false);	
		AFun disjointDataPropFunc = factory.makeAFun(DISJOINT_DATA_PROPERTIES.getShortName(), 2, false);	
		AFun disjointObjPropFunc = factory.makeAFun(DISJOINT_OBJECT_PROPERTIES.getShortName(), 2, false);	
		AFun disjointUnionFunc = factory.makeAFun(DISJOINT_UNION.getShortName(), 3, false);		
		AFun entityAnnoFunc = factory.makeAFun(ENTITY_ANNOTATION.getShortName(), 3, false);	
		AFun entityAnnoAxiomFunc = factory.makeAFun("EntityAnno", 1, false);	
		AFun eqClassFunc = factory.makeAFun(EQUIVALENT_CLASSES.getShortName(), 2, false);			
		AFun eqDataPropFunc = factory.makeAFun(EQUIVALENT_DATA_PROPERTIES.getShortName(), 2, false);	
		AFun eqObjPropFunc = factory.makeAFun(EQUIVALENT_OBJECT_PROPERTIES.getShortName(), 2, false);
		AFun funcDataPropFunc = factory.makeAFun(FUNCTIONAL_DATA_PROPERTY.getShortName(), 2, false);
		AFun funcObjPropFunc = factory.makeAFun(FUNCTIONAL_OBJECT_PROPERTY.getShortName(), 2, false);
		AFun invFuncObjPropFunc = factory.makeAFun(INVERSE_FUNCTIONAL_OBJECT_PROPERTY.getShortName(), 2, false);
		AFun irrefFuncObjPropFunc = factory.makeAFun(IRREFLEXIVE_OBJECT_PROPERTY.getShortName(), 2, false);
		// AFun importsFunc = factory.makeAFun(IMPORTS.getShortName(), 2, false);
		AFun importsFunc = factory.makeAFun(IMPORTS.getShortName(), 1, false);
		AFun invObjPropFunc = factory.makeAFun(INVERSE_OBJECT_PROPERTIES.getShortName(), 3, false);
		AFun negDataPropAssertionFunc = factory.makeAFun(NEGATIVE_DATA_PROPERTY_ASSERTION.getShortName(), 4, false);
		AFun negObjPropAssertionFunc = factory.makeAFun(NEGATIVE_OBJECT_PROPERTY_ASSERTION.getShortName(), 4, false);
		AFun objPropAssertionFunc = factory.makeAFun(OBJECT_PROPERTY_ASSERTION.getShortName(), 4, false);
		AFun subObjPropChainFunc = factory.makeAFun(SUB_OBJECT_PROPERTY_CHAIN.getShortName(), 1, false);
		AFun objPropExpressionFunc = factory.makeAFun("OPExpression", 1, false);
		AFun subObjPropOfFunc = factory.makeAFun(SUB_OBJECT_PROPERTY_OF.getShortName(), 3, false);
		AFun objPropDomainFunc = factory.makeAFun(OBJECT_PROPERTY_DOMAIN.getShortName(), 3, false);
		AFun objPropRangeFunc = factory.makeAFun(OBJECT_PROPERTY_RANGE.getShortName(), 3, false);
		AFun refObjPropFunc = factory.makeAFun(REFLEXIVE_OBJECT_PROPERTY.getShortName(), 2, false);
		AFun subClassOfFunc = factory.makeAFun(SUB_CLASS_OF.getShortName(), 3, false);
		AFun symObjPropFunc = factory.makeAFun(SYMMETRIC_OBJECT_PROPERTY.getShortName(), 2, false);
		AFun transObjPropFunc = factory.makeAFun(TRANSITIVE_OBJECT_PROPERTY.getShortName(), 2, false);	
		AFun classFunc = factory.makeAFun("OWLClass", 1, false);
		AFun entityClassFunc = factory.makeAFun("OWLClassEntity", 1, false);
		
		AFun sameIndFunc = factory.makeAFun("SameIndividual", 2, false);
		AFun UntypedConstantFunc = factory.makeAFun("UntypedConstant", 1, false);
		AFun typedConstantFunc = factory.makeAFun("TypedConstant", 1, false);
		AFun dataTypeFunc = factory.makeAFun("DRDatatype", 1, false);
		
}
