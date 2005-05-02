
import org.semanticweb.owl.model.helper.OWLObjectVisitorAdapter;
import java.io.PrintWriter;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.model.OWLIndividual;
import org.semanticweb.owl.model.OWLObjectProperty;
import org.semanticweb.owl.model.OWLDataProperty;
import org.semanticweb.owl.model.OWLEquivalentClassesAxiom;
import java.util.Iterator;
import org.semanticweb.owl.model.OWLDescription;
import org.semanticweb.owl.model.OWLDisjointClassesAxiom;
import org.semanticweb.owl.model.OWLSubClassAxiom;
import java.io.StringWriter;
import org.semanticweb.owl.model.OWLException;
import org.semanticweb.owl.model.OWLEnumeration;
import org.semanticweb.owl.model.OWLObjectSomeRestriction;
import org.semanticweb.owl.model.OWLObjectAllRestriction;
import org.semanticweb.owl.model.OWLObjectCardinalityRestriction;
import org.semanticweb.owl.model.OWLOr;
import org.semanticweb.owl.model.OWLNot;
import org.semanticweb.owl.model.OWLAnd;
import org.semanticweb.owl.model.OWLObjectValueRestriction;
import org.semanticweb.owl.model.OWLDataValue;
import org.semanticweb.owl.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owl.model.OWLSameIndividualsAxiom;
import java.util.Set;
import java.util.Map;
import org.semanticweb.owl.model.OWLDataType;
import org.semanticweb.owl.model.OWLDescriptionVisitor;
import org.semanticweb.owl.model.OWLClassAxiomVisitor;
import org.semanticweb.owl.model.OWLIndividualAxiomVisitor;
import org.semanticweb.owl.model.OWLEquivalentPropertiesAxiom;
import org.semanticweb.owl.model.OWLSubPropertyAxiom;
import org.semanticweb.owl.model.OWLProperty;
import org.semanticweb.owl.model.OWLDataCardinalityRestriction;
import org.semanticweb.owl.model.OWLDataValueRestriction;
import org.semanticweb.owl.io.abstract_syntax.Renderer;
import org.semanticweb.owl.io.vocabulary.XMLSchemaSimpleDatatypeVocabulary;
import org.semanticweb.owl.model.OWLDataSomeRestriction;
import org.semanticweb.owl.model.OWLDataAllRestriction;
import org.semanticweb.owl.model.OWLDataEnumeration;
import org.semanticweb.owl.model.OWLOntology;
import java.net.URI;
import org.semanticweb.owl.io.ShortFormProvider;

// Generated package name

/**
 * RenderingVisitor.java
 * 
 * 
 * Created: Fri Feb 21 10:57:24 2003
 * 
 * @author Sean Bechhofer
 * @version $Id: RenderingVisitor.java,v 1.7 2004/03/30 17:46:38 sean_bechhofer
 *          Exp $
 */

public class RenderingVisitor2 extends OWLObjectVisitorAdapter {

	ShortFormProvider shortForms;

	StringWriter sw;

	PrintWriter pw;

	int level;

	boolean indenting = true;

	OWLOntology ontology;

	public RenderingVisitor2(ShortFormProvider shortForms, OWLOntology ontology) {
		this.shortForms = shortForms;
		this.ontology = ontology;
		reset();
	}

	public String result() {
		return sw.toString();
	}

	public void reset() {
		sw = new StringWriter();
		pw = new PrintWriter(sw);
	}

	public void visit(OWLClass clazz) throws OWLException {
		pw.print("DC(\"" + shortForms.shortForm(clazz.getURI()) + "\")");
	}

	public void visit(OWLIndividual ind) throws OWLException {
		pw.print("\"" + shortForms.shortForm(ind.getURI()) + "\"");
		
//		
//		RenderingVisitor2 visitor = new RenderingVisitor2(shortForms, ontology);
//		if (ind.isAnonymous()) {
//			/* We need to print out the entire description... */
//			pw.print("Individual(_");
//			if (ind.getTypes(ontology).isEmpty()
//					&& ind.getObjectPropertyValues(ontology).keySet().isEmpty()
//					&& ind.getDataPropertyValues(ontology).keySet().isEmpty()) {
//				pw.print(")");
//			} else {
//				for (Iterator it = ind.getTypes(ontology).iterator(); it
//						.hasNext();) {
//					OWLDescription eq = (OWLDescription) it.next();
//					visitor.reset();
//					eq.accept(visitor);
//					pw.print(",Type(" + visitor.result() + ")");
//				}
//				Map propertyValues = ind.getObjectPropertyValues(ontology);
//
//				for (Iterator it = propertyValues.keySet().iterator(); it
//						.hasNext();) {
//					OWLObjectProperty prop = (OWLObjectProperty) it.next();
//					Set vals = (Set) propertyValues.get(prop);
//					for (Iterator valIt = vals.iterator(); valIt.hasNext();) {
//						OWLIndividual oi = (OWLIndividual) valIt.next();
//						visitor.reset();
//						oi.accept(visitor);
//						pw.print(",Value(" + "\""
//								+ shortForms.shortForm(prop.getURI()) + "\","
//								+ visitor.result() + ")");
//					}
//				}
//				Map dataValues = ind.getDataPropertyValues(ontology);
//
//				for (Iterator it = dataValues.keySet().iterator(); it.hasNext();) {
//					OWLDataProperty prop = (OWLDataProperty) it.next();
//					Set vals = (Set) dataValues.get(prop);
//					for (Iterator valIt = vals.iterator(); valIt.hasNext();) {
//						OWLDataValue dtv = (OWLDataValue) valIt.next();
//						visitor.reset();
//						dtv.accept(visitor);
//						pw.print(",Value(" + "\""
//								+ shortForms.shortForm(prop.getURI()) + "\","
//								+ visitor.result() + ")");
//						if (it.hasNext()) {
//							pw.print(",");
//						}
//					}
//				}
//				pw.print(")");
//			}
//		} else {
//			pw.print("\"" + shortForms.shortForm(ind.getURI()) + "\"");
//		}
	}

	public void visit(OWLObjectProperty prop) throws OWLException {
		// System.out.println("ObjectProperty in RV: " + prop.toString());
		pw.print("\"" + shortForms.shortForm(prop.getURI()) + "\"");
	}

	public void visit(OWLDataProperty prop) throws OWLException {
		// System.out.println("DataProperty in RV: " + prop.toString());
		pw.print("\"" + shortForms.shortForm(prop.getURI()) + "\"");
	}

	public void visit(OWLDataValue cd) throws OWLException {

		// pw.print("\"" + Renderer.escape(cd.getValue()) + "\"");
		String data = Renderer.escape(cd.getValue());

		URI dvdt = cd.getURI();
		String dvlang = cd.getLang();
		if (dvdt != null) {
			pw
					.print("TypedL((\"" + data + "\",\"<" + dvdt.toString()
							+ ">\"))");
			// pw.print("^^" + "<" + dvdt.toString() + ">");
		} else if (dvlang != null) {
			pw.print("PlainL((\"" + data + "\",\"" + dvlang + "\"))");
			// pw.print("@" + dvlang);
		} else
			pw.print("Plain(\"" + data + "\")");

	}

	public void visit(OWLAnd and) throws OWLException {
		pw.print("IntersectionOf([");
		for (Iterator it = and.getOperands().iterator(); it.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print("])");
	}

	public void visit(OWLOr or) throws OWLException {
		pw.print("UnionOf([");
		for (Iterator it = or.getOperands().iterator(); it.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print("])");
	}

	public void visit(OWLNot not) throws OWLException {
		pw.print("ComplementOf(");
		OWLDescription desc = (OWLDescription) not.getOperand();
		desc.accept(this);
		pw.print(")");
	}

	public void visit(OWLEnumeration enumeration) throws OWLException {
		pw.print("OneOfDes([");
		for (Iterator it = enumeration.getIndividuals().iterator(); it
				.hasNext();) {
			OWLIndividual desc = (OWLIndividual) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print("])");
	}

	public void visit(OWLObjectSomeRestriction restriction) throws OWLException {
		pw.print("DR(IndivRestriction(");
		restriction.getObjectProperty().accept(this);
		pw.print(",IRCSomeValuesFrom(");
		restriction.getDescription().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLObjectAllRestriction restriction) throws OWLException {
		pw.print("DR(IndivRestriction(");
		restriction.getObjectProperty().accept(this);
		pw.print(",IRCAllValuesFrom(");
		restriction.getDescription().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLObjectValueRestriction restriction)
			throws OWLException {
		pw.print("DR(IndivRestriction(");
		restriction.getObjectProperty().accept(this);
		/* Changed from hasValue */
		pw.print(",IRCValue(");
		restriction.getIndividual().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLDataSomeRestriction restriction) throws OWLException {
		pw.print("DR(DataRestriction(");
		restriction.getDataProperty().accept(this);
		pw.print(",DRCSomeValuesFrom (");
		restriction.getDataType().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLDataAllRestriction restriction) throws OWLException {
		pw.print("DR(DataRestriction(");
		restriction.getDataProperty().accept(this);
		pw.print(",DRCAllValuesFrom(");
		restriction.getDataType().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLObjectCardinalityRestriction restriction)
			throws OWLException {
		pw.print("DR(IndivRestriction(");
		restriction.getObjectProperty().accept(this);
		if (restriction.isExactly()) {
			pw.print(",IRCCardinality( Cardinality ("
					+ restriction.getAtLeast() + ")), []))");
		} else if (restriction.isAtMost()) {
			pw.print(",IRCCardinality( MaxCardinality("
					+ restriction.getAtMost() + ")), []))");
		} else if (restriction.isAtLeast()) {
			pw.print(",IRCCardinality( MinCardinality("
					+ restriction.getAtLeast() + ")), []))");
		} else
			pw.print("))");
	}

	public void visit(OWLDataCardinalityRestriction restriction)
			throws OWLException {
		pw.print("DR(DataRestriction(");
		restriction.getDataProperty().accept(this);
		if (restriction.isExactly()) {
			pw.print(",DRCCardinality(Cardinality(" + restriction.getAtLeast()
					+ ")), []))");
		} else if (restriction.isAtMost()) {
			pw.print(",DRCCardinality(MaxCardinality("
					+ restriction.getAtMost() + ")), []))");
		} else if (restriction.isAtLeast()) {
			pw.print(",DRCCardinality(MinCardinality("
					+ restriction.getAtLeast() + ")), []))");
		} else
			pw.print("))");

	}

	public void visit(OWLDataValueRestriction restriction) throws OWLException {
		pw.print("DR(DataRestriction(");
		restriction.getDataProperty().accept(this);
		/* Changed from hasValue */
		pw.print(",DRCValue(");
		restriction.getValue().accept(this);
		pw.print("),[]))");
	}

	public void visit(OWLEquivalentClassesAxiom axiom) throws OWLException {
		pw.print("EquivalentClasses(");
		for (Iterator it = axiom.getEquivalentClasses().iterator(); it
				.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

	public void visit(OWLDisjointClassesAxiom axiom) throws OWLException {
		pw.print("DisjointClasses(");
		for (Iterator it = axiom.getDisjointClasses().iterator(); it.hasNext();) {
			OWLDescription desc = (OWLDescription) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

	public void visit(OWLSubClassAxiom axiom) throws OWLException {
		pw.print("SubClassOf(");
		axiom.getSubClass().accept(this);
		pw.print(",");
		axiom.getSuperClass().accept(this);
		pw.print(")");
	}

	public void visit(OWLEquivalentPropertiesAxiom axiom) throws OWLException {
		pw.print("EquivalentProperties(");
		for (Iterator it = axiom.getProperties().iterator(); it.hasNext();) {
			OWLProperty prop = (OWLProperty) it.next();
			prop.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

	public void visit(OWLSubPropertyAxiom axiom) throws OWLException {
		pw.print("SubPropertyOf(");
		axiom.getSubProperty().accept(this);
		pw.print(",");
		axiom.getSuperProperty().accept(this);
		pw.print(")");
	}

	public void visit(OWLDifferentIndividualsAxiom ax) throws OWLException {
		pw.print("DifferentIndividuals(");
		for (Iterator it = ax.getIndividuals().iterator(); it.hasNext();) {
			OWLIndividual desc = (OWLIndividual) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

	public void visit(OWLSameIndividualsAxiom ax) throws OWLException {
		pw.print("SameIndividual(");
		for (Iterator it = ax.getIndividuals().iterator(); it.hasNext();) {
			OWLIndividual desc = (OWLIndividual) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

	public void visit(OWLDataType ocdt) throws OWLException {
		pw.print(shortForms.shortForm(ocdt.getURI()));
	}

	public void visit(OWLDataEnumeration enumeration) throws OWLException {
		pw.print("OneOfData(");
		for (Iterator it = enumeration.getValues().iterator(); it.hasNext();) {
			OWLDataValue desc = (OWLDataValue) it.next();
			desc.accept(this);
			if (it.hasNext()) {
				pw.print(",");
			}
		}
		pw.print(")");
	}

} // RenderingVisitor

