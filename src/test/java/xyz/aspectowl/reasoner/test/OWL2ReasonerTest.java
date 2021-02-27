package xyz.aspectowl.reasoner.test;

import net.sf.tweety.logics.fol.reasoner.FolReasoner;
import net.sf.tweety.logics.fol.syntax.FolFormula;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.model.*;
import xyz.aspectowl.tptp.reasoner.SpassTptpFolReasoner;
import xyz.aspectowl.tptp.renderer.OWL2TPTPObjectRenderer;
import xyz.aspectowl.tptp.renderer.OWL2TPTPRenderer;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.Arrays;
import java.util.Optional;

/**
 * @author ralph
 */
public class OWL2ReasonerTest {

    private static final IRI conjectureProp = IRI.create("http://ontology.aspectowl.xyz/reasoner/aspectowl2tptp/test/base#conjecture");

    private OWLOntologyManager man;
    private FolReasoner prover;

    private String spassLocation;

    @Before
    public void setup() {
        spassLocation = Optional.of(System.getenv("SPASS_HOME")).orElseThrow(() -> new IllegalStateException("SPASS_HOME environment variable must point to SPASS installation directory"));

        man = OWLManager.createOWLOntologyManager();
        man.getIRIMappers().add(ontologyIRI -> IRI.create(OWL2ReasonerTest.class.getResource("/ontologies/test-base.ofn")));

        FolReasoner.setDefaultReasoner(new SpassTptpFolReasoner(spassLocation)); //Set default prover, options are NaiveProver, EProver, Prover9
        prover = FolReasoner.getDefaultReasoner();
    }

    @Test
    public void reasonOnOntologies() throws URISyntaxException {
        URL ontologiesBaseURL = OWL2ReasonerTest.class.getResource("/ontologies");
        File ontologiesBaseDir = new File(ontologiesBaseURL.toURI());
        Arrays.stream(ontologiesBaseDir.listFiles(file -> !file.getName().equals("test-base.ofn") && file.getName().endsWith(".ofn"))).forEach(file -> {
            try {
                OWLOntology onto = man.loadOntologyFromOntologyDocument(OWL2ReasonerTest.class.getResourceAsStream("/ontologies/" + file.getName()));
                OWL2TPTPObjectRenderer renderer = new OWL2TPTPObjectRenderer(onto, new PrintWriter(System.out));
                onto.accept(renderer);
                onto.annotations(man.getOWLDataFactory().getOWLAnnotationProperty(conjectureProp)).forEach(annotation ->
                        annotation.getValue().asLiteral().ifPresent(literal -> {
                            try {
                                assertTrue(prover.query(renderer.getBeliefSet(), (FolFormula) renderer.getFolParser().parseFormula(literal.getLiteral())));
                            } catch (IOException e) {
                                throw new RuntimeException(e);
                            }
                        }));
            } catch (OWLOntologyCreationException e) {
                throw new RuntimeException(e);
            }
        });

    }
}
