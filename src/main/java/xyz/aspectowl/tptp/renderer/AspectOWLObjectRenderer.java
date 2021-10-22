package xyz.aspectowl.tptp.renderer;

import net.sf.tweety.logics.fol.syntax.FolFormula;
import org.semanticweb.owlapi.model.*;

import java.util.stream.Stream;

/**
 *
 * @author ralph
 */
public interface AspectOWLObjectRenderer<T> {

    default boolean hasAspect(OWLAxiom axiom) {
        return false;
    }

    public T handleAspects(OWLAxiom axiom, Stream<FolFormula> nonAspectFormulae);
}
