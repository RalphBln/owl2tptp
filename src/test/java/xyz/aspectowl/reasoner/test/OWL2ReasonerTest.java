package xyz.aspectowl.reasoner.test;

import net.sf.tweety.logics.fol.parser.FolParser;
import net.sf.tweety.logics.fol.reasoner.FolReasoner;
import net.sf.tweety.logics.fol.syntax.FolBeliefSet;
import net.sf.tweety.logics.fol.syntax.FolFormula;
import net.sf.tweety.logics.fol.writer.TPTPWriter;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import xyz.aspectowl.tptp.reasoner.SpassTptpFolReasoner;
import xyz.aspectowl.tptp.renderer.AspectAnnotationOWL2TPTPObjectRenderer;
import xyz.aspectowl.tptp.renderer.OWL2TPTPObjectRenderer;

import java.io.*;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.Arrays;
import java.util.Optional;
import java.util.stream.Stream;

import static org.junit.Assert.assertTrue;

/**
 * @author ralph
 */
public class OWL2ReasonerTest {

    private static final IRI conjectureProp = IRI.create("http://ontology.aspectowl.xyz/reasoner/aspectowl2tptp/test/base#conjecture");

    private static FolReasoner prover;

    @BeforeAll
    public static void setup() {
        String spassLocation = Optional.of(System.getenv("SPASS_HOME")).orElseThrow(() -> new IllegalStateException("SPASS_HOME environment variable must point to SPASS installation directory"));
        FolReasoner.setDefaultReasoner(new SpassTptpFolReasoner(spassLocation)); //Set default prover, options are NaiveProver, EProver, Prover9
        prover = FolReasoner.getDefaultReasoner();
    }

    @ParameterizedTest
    @MethodSource("provideOntologySourceLocations")
    public void reasonOnOntologies(FolBeliefSet bs, FolFormula conjecture)  {
        try {
            PrintWriter out = new PrintWriter(System.out);
            TPTPWriter w = new TPTPWriter(out);
            w.printBase(bs);
            w.printQuery(conjecture);
            out.flush();
        } catch (IOException e) {
            e.printStackTrace();
        }
        System.out.printf(((SpassTptpFolReasoner)prover).queryProof(bs, conjecture));
        assertTrue(prover.query(bs, conjecture));
    }

    private static Stream<Arguments> provideOntologySourceLocations() throws URISyntaxException {

        OWLOntologyManager man = OWLManager.createOWLOntologyManager();
        man.getIRIMappers().add(ontologyIRI -> IRI.create(OWL2ReasonerTest.class.getResource("/ontologies/test-base.ofn")));

        URL ontologiesBaseURL = OWL2ReasonerTest.class.getResource("/ontologies");
        File ontologiesBaseDir = new File(ontologiesBaseURL.toURI());

        OWLAnnotationProperty conjectureAnnotationProperty = man.getOWLDataFactory().getOWLAnnotationProperty(conjectureProp);

        return Arrays.stream(ontologiesBaseDir.listFiles(file -> !file.getName().equals("test-base.ofn") && file.getName().endsWith(".ofn"))).flatMap(file -> {
            try {
                OWLOntology onto = man.loadOntologyFromOntologyDocument(OWL2ReasonerTest.class.getResourceAsStream("/ontologies/" + file.getName()));
                AspectAnnotationOWL2TPTPObjectRenderer renderer = new AspectAnnotationOWL2TPTPObjectRenderer(onto, new PrintWriter(new PrintStream(OutputStream.nullOutputStream())));
                onto.accept(renderer);
                return onto.getAnnotations().stream().filter(annotation -> annotation.getProperty().equals(conjectureAnnotationProperty)).map(annotation ->
                      Arguments.of(renderer.getBeliefSet(), parseFormula(annotation.getValue().asLiteral().get().getLiteral(), renderer.getFolParser()).orElseThrow(() -> new RuntimeException()))
                );
            } catch (OWLOntologyCreationException e) {
                throw new RuntimeException(e);
            }
        });
    }

    private static Optional<FolFormula> parseFormula(String formula, FolParser parser) {
        FolFormula result = null;
        try {
            result = parser.parseFormula(formula);
        } catch (IOException e) {
            return Optional.empty();
        }
        return Optional.of(result);
    }
}
