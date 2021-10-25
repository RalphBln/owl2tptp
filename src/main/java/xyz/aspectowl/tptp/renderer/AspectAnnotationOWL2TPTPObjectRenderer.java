package xyz.aspectowl.tptp.renderer;

import net.sf.tweety.logics.fol.syntax.FolFormula;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.expression.OWLClassExpressionParser;
import org.semanticweb.owlapi.manchestersyntax.parser.ManchesterOWLSyntaxFramesParser;
import org.semanticweb.owlapi.manchestersyntax.parser.ManchesterOWLSyntaxParserImpl;
import org.semanticweb.owlapi.model.*;

import java.io.PrintWriter;
import java.util.stream.Stream;

/**
 * @author ralph
 */
public class AspectAnnotationOWL2TPTPObjectRenderer extends AspectOWL2TPTPObjectRenderer {

    private static final IRI aspectAnnotationProperty = IRI.create("http://ontology.aspectowl.xyz#hasAspect");

    public AspectAnnotationOWL2TPTPObjectRenderer(OWLOntology ontology, PrintWriter writer) {
        super(ontology, writer);
    }

    private final OWLOntologyManager man = OWLManager.createOWLOntologyManager();
    private final ManchesterOWLSyntaxParserImpl parser = new ManchesterOWLSyntaxParserImpl(new OntologyConfigurator(), man.getOWLDataFactory());

    @Override
    public boolean hasAspect(OWLAxiom axiom) {
        return axiom.isAnnotated() && axiom.annotations().filter(a -> a.getProperty().getIRI().equals(aspectAnnotationProperty)).findAny().map(c -> true).get();
    }

    @Override
    public Stream<FolFormula> handleAspects(OWLAxiom axiom, Stream<FolFormula> nonAspectFormulae) {
        axiom.signature().forEach(entity -> entity.);
        axiom.annotations()
                .filter(a -> a.getProperty().getIRI().equals(aspectAnnotationProperty))
//                .filter(a -> a.annotationValue().isAnonymousExpression() && a.annotationValue().nestedClassExpressions());
                .forEach(a -> System.out.println("*** Aspect *** " + a.getValue()));
        Stream<FolFormula> aspectFormulae = Stream.empty(); // TODO
        return Stream.concat(nonAspectFormulae, aspectFormulae);
    }



    }
}
