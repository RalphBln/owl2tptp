package xyz.aspectowl.tptp.renderer;

import net.sf.tweety.logics.fol.syntax.FolFormula;
import org.semanticweb.owlapi.manchestersyntax.parser.ManchesterOWLSyntaxParserImpl;
import org.semanticweb.owlapi.model.*;

import java.io.PrintWriter;
import java.util.stream.Stream;

/**
 * @author ralph
 */
public class AspectAnnotationOWL2TPTPObjectRenderer extends AspectOWL2TPTPObjectRenderer {

    private static final IRI aspectAnnotationProperty = IRI.create("http://ontology.aspectowl.xyz#hasAspect");

    private final ManchesterOWLSyntaxParserImpl manchesterSyntaxParser;

    public AspectAnnotationOWL2TPTPObjectRenderer(OWLOntology ontology, PrintWriter writer) {
        super(ontology, writer);
        manchesterSyntaxParser = new ManchesterOWLSyntaxParserImpl(new OntologyConfigurator(), ontology.getOWLOntologyManager().getOWLDataFactory());
        manchesterSyntaxParser.getPrefixManager().setDefaultPrefix("");
        manchesterSyntaxParser.getPrefixManager().setPrefix("", ontology.getOntologyID().getOntologyIRI().get().toString() + "#");
        manchesterSyntaxParser.setDefaultOntology(ontology);
    }


    @Override
    public boolean hasAspect(OWLAxiom axiom) {
        return axiom.isAnnotated() && axiom.annotations().filter(a -> a.getProperty().getIRI().equals(aspectAnnotationProperty)).findAny().map(c -> true).get();
    }

    @Override
    public Stream<FolFormula> handleAspects(OWLAxiom axiom, Stream<FolFormula> nonAspectFormulae) {
        axiom.annotations()
                .filter(a -> a.getProperty().getIRI().equals(aspectAnnotationProperty))
                .filter(a -> a.annotationValue().isLiteral())
                .forEach(a -> a.getValue().asLiteral().ifPresent(literal -> {
                    manchesterSyntaxParser.setStringToParse(literal.getLiteral());
                    OWLClassExpression aspect = manchesterSyntaxParser.parseClassExpression();
                    System.out.println(aspect);
                }));

        Stream<FolFormula> aspectFormulae = Stream.empty(); // TODO
        return Stream.concat(nonAspectFormulae, aspectFormulae);
    }
}
