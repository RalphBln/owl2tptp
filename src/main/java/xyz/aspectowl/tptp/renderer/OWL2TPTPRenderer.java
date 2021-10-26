package xyz.aspectowl.tptp.renderer;

import org.semanticweb.owlapi.io.AbstractOWLRenderer;
import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.io.OWLRendererIOException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLRuntimeException;

import java.io.PrintWriter;

/**
 * @author ralph
 */
public class OWL2TPTPRenderer extends AbstractOWLRenderer {
    @Override
    public void render(OWLOntology ontology, PrintWriter writer) throws OWLRendererException {
        try {
            AspectAnnotationOWL2TPTPObjectRenderer ren = new AspectAnnotationOWL2TPTPObjectRenderer(ontology,
                    writer);
            ontology.accept(ren);
            writer.flush();
        } catch (OWLRuntimeException e) {
            throw new OWLRendererIOException(e);
        }
    }
}
