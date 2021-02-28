package xyz.aspectowl.tptp.renderer;

import com.sun.istack.Nullable;
import net.sf.tweety.commons.ParserException;
import net.sf.tweety.commons.util.Pair;
import net.sf.tweety.logics.commons.syntax.Constant;
import net.sf.tweety.logics.commons.syntax.Predicate;
import net.sf.tweety.logics.fol.parser.FolParser;
import net.sf.tweety.logics.fol.reasoner.FolReasoner;
import net.sf.tweety.logics.fol.syntax.FolBeliefSet;
import net.sf.tweety.logics.fol.syntax.FolFormula;
import net.sf.tweety.logics.fol.syntax.FolSignature;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.PrefixDocumentFormat;
import org.semanticweb.owlapi.io.XMLUtils;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.util.AnnotationValueShortFormProvider;
import org.semanticweb.owlapi.util.DefaultPrefixManager;
import org.semanticweb.owlapi.util.ShortFormProvider;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import xyz.aspectowl.tptp.reasoner.SpassTptpFolReasoner;
import xyz.aspectowl.tptp.reasoner.util.UnsortedTPTPWriter;

import javax.validation.constraints.NotNull;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

// TODO include ontology import closure (priority HIGH)
// TODO prevent name clashes (since we only use local names)
// TODO handle punnings (make unique names)  (priority MEDIUM) DONE
// TODO prevent name clashes between existing and generated predicate names (unlikely but who knows)  (priority LOW)


/**
 * @author ralph
 *
 * Prefixes:
 *
 * nc: named class
 * ni: named individual
 * no: named object property
 * nd: named data property
 *
 * tc: temporary (anonymous) class (such as "r some A")
 * to: temporary (anonymous) object property (such as "inverse of r")
 *
 * owl: owl built-entity names (owlThing and owlNothing)
 */
public class OWL2TPTPObjectRenderer implements OWLObjectVisitor {

    private static final Logger log = LoggerFactory.getLogger(OWL2TPTPObjectRenderer.class);

    protected final Optional<OWLOntology> onto;
    private DefaultPrefixManager defaultPrefixManager;
    protected Optional<ShortFormProvider> labelMaker = Optional.empty();
    private Optional<PrefixManager> prefixManager = Optional.empty();
    private boolean writeEntitiesAsURIs = true;
    private boolean addMissingDeclarations = true;

    private UnsortedTPTPWriter out;

    public FolParser getFolParser() {
        return folp;
    }

    private FolParser folp;

    public FolBeliefSet getBeliefSet() {
        return bs;
    }

    // There is a DlBeliefSet and I considered using it (somehow shove the OWL2 KB into a DLBeliefSet and then maybe
    // transform the latter to a FolBeliedSet) but it turned out DLBeliefSet only implements ALC while we need full
    // SROIQ(D).
    private FolBeliefSet bs;
    private FolSignature sig;

    public OWL2TPTPObjectRenderer(@Nullable OWLOntology ontology, PrintWriter writer) {
        onto = Optional.ofNullable(ontology);
        out = new UnsortedTPTPWriter(writer);
        defaultPrefixManager = new DefaultPrefixManager();
        onto.ifPresent(o -> {
            OWLDocumentFormat ontologyFormat = o.getNonnullFormat();
            // reuse the setting on the existing format
            addMissingDeclarations = ontologyFormat.isAddMissingTypes();
            if (ontologyFormat instanceof PrefixDocumentFormat) {
                prefixManager = Optional.of(new DefaultPrefixManager());
                prefixManager.get().copyPrefixesFrom((PrefixDocumentFormat) ontologyFormat);
                prefixManager.get().setPrefixComparator(
                        ((PrefixDocumentFormat) ontologyFormat).getPrefixComparator());
                if (!o.isAnonymous() && prefixManager.get().getDefaultPrefix() == null) {
                    prefixManager.get().setDefaultPrefix(XMLUtils.iriWithTerminatingHash(
                            o.getOntologyID().getOntologyIRI().get().toString()));
                }
            }
            OWLOntologyManager manager = o.getOWLOntologyManager();
            OWLDataFactory df = manager.getOWLDataFactory();
            labelMaker = Optional.of(
                    new AnnotationValueShortFormProvider(Collections.singletonList(df.getRDFSLabel()),
                            Collections.emptyMap(), manager, defaultPrefixManager));
        });
    }

    /**
     * Translates an IRI to a FOL constant name
     * @param iri
     * @return
     */
    private String translateIRI(@NotNull HasIRI iri) {
        String prefix;
        if (iri instanceof OWLClass)
            prefix = "nc"; // named class
        else if (iri instanceof OWLIndividual)
            prefix = "ni"; // named individual
        else if (iri instanceof OWLObjectProperty)
            prefix = "no"; // named object property
        else if (iri instanceof OWLDataProperty)
            prefix = "nd"; // named data property
        else
            prefix = "Error"; // should not happen
        String localName = iri.getIRI().getShortForm().replaceFirst("^.*#(.+?)$", "$1"); // regex is a workaround for https://github.com/owlcs/owlapi/issues/699
        return String.format("%s%s", prefix, localName);
//        return iri.getIRI().toString();
    }

    private String translate(OWLIndividual individual) {
        if (individual.isAnonymous()) {
            throw new IllegalArgumentException(String.format("Cannot translate anonymous individuals to FOL: %s", individual));
        }
        return translateIRI(individual.asOWLNamedIndividual());
    }

    /**
     * Translates the given OWL class expression (CE) to a String representation of its corresponding FOL predicate.
     * Has side effects: Translates all anonymous CEs that the given CE is composed of to temporary named predicates
     * (the names of which correspond to their respective type 3 (name based) UUID generated from the respective String
     * representation of the CE, prefixed by "tc" and minus the "-" characters) and adds formulas that define the
     * complex predicate by using these temporarily named predicates.
     * @param ce
     * @return
     */
    private String translate(OWLClassExpression ce) {
        ClassExpressionType type = ce.getClassExpressionType();
        if (type == ClassExpressionType.OWL_CLASS)
            return translateIRI(ce.asOWLClass());

        String tempName = temporaryPredicate(ce);

        StringBuilder buf = new StringBuilder();
        buf.append("forall X: (%s(X) <=> ");

        switch (type) {
            case OBJECT_SOME_VALUES_FROM: {
                OWLObjectSomeValuesFrom svf = (OWLObjectSomeValuesFrom)ce;
                String opeTrans = translate(svf.getProperty());
                String fillerTrans = translate(svf.getFiller());

                buf.append(String.format("exists Y: (%s(X,Y) && %(Y))", opeTrans, fillerTrans));
                break;
            }
            case OBJECT_ALL_VALUES_FROM: {
                OWLObjectAllValuesFrom avf = (OWLObjectAllValuesFrom) ce;
                String opeTrans = translate(avf.getProperty());
                String fillerTrans = translate(avf.getFiller());

                buf.append(String.format("forall Y: (%s(X,Y) => %s(Y))", opeTrans, fillerTrans));
                break;
            }
            case OBJECT_MIN_CARDINALITY: {
                // forall X: (Temp(X) <=> exists Y1: (r(X,Y1) && Filler(Y1) &&
                //                        exists Y2: (r(X,Y2) && Filler(Y2) &&
                //                        .. &&
                //                        exists Yn: (r(X,Yn) && Filler(Yn) &&
                //                        Y1 /== Y2 /== ... /== Yn
                //                        ))...) [1..n]
                // )
                OWLObjectMinCardinality omc = (OWLObjectMinCardinality) ce;
                String opeTrans = translate(omc.getProperty());
                String fillerTrans = translate(omc.getFiller());
                int cardinality = omc.getCardinality();

                String fragment = "exists Y%d: (%s(X,Y%d) && %s(Y%d)";
                buf.append(String.format(fragment, 0, opeTrans, 0, fillerTrans, 0));
                IntStream.range(1, cardinality).forEach(i -> buf.append(" && ").append(String.format(fragment, i, opeTrans, i, fillerTrans, i)));

                List<Integer> indices = IntStream.range(0, cardinality).boxed().collect(Collectors.toList());
                HashSet<Pair<Integer, Integer>> combinations = combinations(indices, indices);
                combinations.stream().forEach(pair -> buf.append(String.format(" &&  Y%d /== Y%d", pair.getFirst(), pair.getSecond())));

                IntStream.range(0, cardinality).forEach(i -> buf.append(')')); // closing inner existential quantifications
                break;
            }
            case OBJECT_MAX_CARDINALITY: {
                // forall X: (Temp(X) <=> exists Y1: (r(X,Y1) && Filler(Y1) &&
                //                        exists Y2: (r(X,Y2) && Filler(Y2) &&
                //                        .. &&
                //                        exists Yn: (r(X,Yn) && Filler(Yn) &&
                //                        forall Z: (Z /== Y1 /== Y2 /== .. /== Yn => !r(X,Z))
                //                        ))...) [1..n]
                // )
                OWLObjectMaxCardinality omc = (OWLObjectMaxCardinality) ce;
                String opeTrans = translate(omc.getProperty());
                String fillerTrans = translate(omc.getFiller());
                int cardinality = omc.getCardinality();

                String fragment = "exists Y%d: (%s(X,Y%d) && %s(Y%d)";
                buf.append(String.format(fragment, 0, opeTrans, 0, fillerTrans, 0));
                IntStream.range(1, cardinality).forEach(i -> buf.append(" && ").append(String.format(fragment, i, opeTrans, i, fillerTrans, i)));

                buf.append(" && forall Z: ((Z /== Y0 ");
                IntStream.range(1, cardinality).forEach(i -> buf.append(String.format(" && Z /== Y%d", i)));
                buf.append(String.format(") => !%s(X,Z))", opeTrans));

                IntStream.range(0, cardinality).forEach(i -> buf.append(')')); // closing inner existential quantifications
                break;
            }
            case OBJECT_EXACT_CARDINALITY: {
                //
                // forall X: (Temp(X) <=> exists Y1: (r(X,Y1) && Filler(Y1) &&
                //                        exists Y2: (r(X,Y2) && Filler(Y2) &&
                //                        .. &&
                //                        exists Yn: (r(X,Yn) && Filler(Yn) &&
                //                        Y1 /== Y2 /== ... /== Yn &&
                //                        forall Z: (Z /== Y1 /== Y2 /== .. /== Yn => !r(X,Z))
                //                        ))...) [1..n]
                // )
                OWLObjectExactCardinality oec = (OWLObjectExactCardinality) ce;
                String opeTrans = translate(oec.getProperty());
                String fillerTrans = translate(oec.getFiller());
                int cardinality = oec.getCardinality();

                String fragment = "exists Y%d: (%s(X,Y%d) && %s(Y%d)";
                buf.append(String.format(fragment, 0, opeTrans, 0, fillerTrans, 0));
                IntStream.range(1, cardinality).forEach(i -> buf.append(" && ").append(String.format(fragment, i, opeTrans, i, fillerTrans, i)));

                List<Integer> indices = IntStream.range(0, cardinality).boxed().collect(Collectors.toList());
                HashSet<Pair<Integer, Integer>> combinations = combinations(indices, indices);
                combinations.stream().forEach(pair -> buf.append(String.format(" &&  Y%d /== Y%d", pair.getFirst(), pair.getSecond())));

                buf.append(" && forall Z: ((Z /== Y0 ");
                IntStream.range(1, cardinality).forEach(i -> buf.append(String.format(" && Z /== Y%d", i)));
                buf.append(String.format(") => !%s(X,Z))", opeTrans));

                IntStream.range(0, cardinality).forEach(i -> buf.append(')')); // closing inner existential quantifications
                break;
            }
            case OBJECT_HAS_VALUE: {
                OWLObjectHasValue ohv = (OWLObjectHasValue) ce;
                OWLObjectPropertyExpression ope = ohv.getProperty();
                OWLIndividual filler = ohv.getFiller();

                buf.append(String.format("%s(X,%s)", translate(ope), translate(filler)));
                break;
            }
            case OBJECT_HAS_SELF: {
                OWLObjectHasSelf ohs = (OWLObjectHasSelf)ce;
                buf.append(String.format("%s(X,X)", translate(ohs.getProperty())));
                break;
            }
            case OBJECT_INTERSECTION_OF: {
                OWLObjectIntersectionOf oio = (OWLObjectIntersectionOf) ce;
                oio.operands().findFirst().ifPresent(operand -> buf.append(String.format("%s(X)", translate(operand))));
                oio.operands().skip(1).forEach(operand -> buf.append(String.format(" && %s(X)", translate(operand))));
                break;
            }
            case OBJECT_UNION_OF: {
                OWLObjectUnionOf ouo = (OWLObjectUnionOf) ce;
                ouo.operands().findFirst().ifPresent(operand -> buf.append(String.format("%s(X)", translate(operand))));
                ouo.operands().skip(1).forEach(operand -> buf.append(String.format(" || %s(X)", translate(operand))));
                break;
            }
            case OBJECT_COMPLEMENT_OF: {
                OWLObjectComplementOf oco = (OWLObjectComplementOf) ce;
                buf.append(String.format("!%s(X)", translate(oco.getOperand())));
                break;
            }
            case OBJECT_ONE_OF: {
                List<OWLIndividual> individuals = ((OWLObjectOneOf) ce).getOperandsAsList();
                Optional.of(individuals.get(0)).ifPresent(individual -> buf.append(String.format("X == %s", translate(individual))));
                individuals.stream().skip(1).forEach(individual -> buf.append(String.format("|| X == %s", translate(individual))));
                break;
            }
            case DATA_SOME_VALUES_FROM:
                throw new RuntimeException("Not implemented " + type);
            case DATA_ALL_VALUES_FROM:
                throw new RuntimeException("Not implemented " + type);
            case DATA_MIN_CARDINALITY:
                throw new RuntimeException("Not implemented " + type);
            case DATA_MAX_CARDINALITY:
                throw new RuntimeException("Not implemented " + type);
            case DATA_EXACT_CARDINALITY:
                throw new RuntimeException("Not implemented " + type);
            case DATA_HAS_VALUE:
                throw new RuntimeException("Not implemented " + type);

            default:
                log.error("Unhandled class expression type: %s", type);
                throw new RuntimeException("Unknown class expression type " + type);
        }
        buf.append(')');
        addFormula(buf.toString(), tempName);
        return tempName;
    }

    @Override
    public void visit(OWLDifferentIndividualsAxiom axiom) {
        List<OWLIndividual> individuals = axiom.getIndividualsAsList();
        combinations(individuals, individuals).forEach(pair -> addFormula("%s /== %s", translate(pair.getFirst()), translate(pair.getSecond())));
    }

    private <T extends Comparable<? super T>> HashSet<Pair<T, T>> combinations(Collection<T> s1, Collection<T> s2) {
        HashSet<Pair<T, T>> pairs = new HashSet<>();

        s1.forEach(i ->
                s2.stream().filter(j -> !(j.equals(i))).forEach(j ->
                        pairs.add(ordered(new Pair<>(i, j)))
                )
        );
        return pairs;
    }

    public static <T extends Comparable<? super T>> Pair<T, T> ordered(Pair<T, T> pair) {
        T a = pair.getFirst();
        T b = pair.getSecond();
        return a.compareTo(b) < 0 ? pair : new Pair<>(b, a);
    }

    private String temporaryPredicate(OWLObject o) {
        String tempName = UUID.nameUUIDFromBytes(o.toString().getBytes(StandardCharsets.UTF_8)).toString()
                .replaceAll("-", "");
        if(!sig.containsPredicate(tempName)) {
            if (o instanceof OWLClassExpression) {
                tempName = String.format("tc%s", tempName);
                sig.add(new Predicate(tempName, 1));
            } else if (o instanceof OWLObjectPropertyExpression) {
                tempName = String.format("to%s", tempName);
                sig.add(new Predicate(tempName, 2));
            } else {
                throw new IllegalArgumentException("Can only make temporary predicated out of classes or object properties.");
            }
            bs.setSignature(sig);
        }
        return tempName;
    }

    private String translate(OWLObjectPropertyExpression ope) {
        if (ope.isNamed()) {
            return translateIRI(ope.asOWLObjectProperty());
        }

        // the only possible anonymous object property expression is an inverse property expression
        OWLObjectProperty op = ((OWLObjectInverseOf)ope).getInverse().asOWLObjectProperty();
        String tempName = temporaryPredicate(op);
        addFormula("forall X: (forall Y: (%s(X,Y) <=> %s(Y,X)))", translateIRI(op), tempName);

        return tempName;
    }

    private void addFormula(String format, Object... args) {
        try {
            bs.add((FolFormula)folp.parseFormula(String.format(format, args)));
        } catch (IOException e) {
            throw new ParserException(e);
        }
    }

    @Override
    public void visit(OWLOntology ontology) {
        // signature
        sig = new FolSignature(true);
        sig.add(new Predicate("owlThing", 1));
        sig.add(new Predicate("owlNothing", 1));
        ontology.signature(Imports.INCLUDED).forEach(entity -> entity.accept(this));

        folp = new FolParser(false);
        folp.setSignature(sig);

        // axioms
        bs = new FolBeliefSet();
        bs.setSignature(sig);
        try {
            bs.add(folp.parseFormula("forall X: (owlThing(X))"));
            bs.add(folp.parseFormula("forall X: (!owlNothing(X))"));
        } catch (IOException e) {
            throw new OWL2TPTPRendererError(String.format("Error configuring %s. Could not parse trivial formula. This should not have happened.", OWL2TPTPObjectRenderer.class.getSimpleName()), e);
        }
        ontology.axioms().forEach(axiom -> axiom.accept(this));

        try {
            out.printBase(bs);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void visit(OWLClass ce) {
        log.debug("Class: %s\n", ce);
        sig.add(new Predicate(translate(ce), 1));
    }

    @Override
    public void visit(OWLNamedIndividual individual) {
        log.debug("Individual: %s\n", individual);
        sig.add(new Constant(translateIRI(individual)));
    }

    @Override
    public void visit(OWLObjectProperty property) {
        log.debug("ObjectProperty: %s\n", property);
        sig.add(new Predicate(translateIRI(property), 2));
    }

    @Override
    public void visit(OWLClassAssertionAxiom axiom) {
        String individualTrans = translate(axiom.getIndividual());
        String ceTrans = translate(axiom.getClassExpression());
        addFormula("%s(%s)", ceTrans, individualTrans);
    }

    @Override
    public void visit(OWLObjectPropertyAssertionAxiom axiom) {
        OWLIndividual subject = axiom.getSubject();
        OWLObjectPropertyExpression predicate = axiom.getProperty();
        OWLIndividual object = axiom.getObject();
        addFormula("%s(%s,%s)", translate(predicate), translate(subject), translate(object));
    }

    @Override
    public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
        OWLObjectPropertyExpression ope = axiom.getProperty();
        String predicateName = translateIRI(axiom.getProperty().asOWLObjectProperty());
        addFormula("forall X: (forall Y: (forall Z: (%s(X,Y) && %s(Y,Z) => %s(X,Z))))", predicateName, predicateName, predicateName);
        log.debug("OWLTransitiveObjectPropertyAxiom: %s\n", axiom);
    }

    @Override
    public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
        OWLObjectPropertyExpression ope = axiom.getProperty();
        String predicateName = translate(ope);
        addFormula("forall X: (%s(X,X))", predicateName);
        log.debug("OWLReflexiveObjectPropertyAxiom: %s\n", axiom);
    }

    @Override
    public void visit(OWLSubClassOfAxiom axiom) {
        OWLClassExpression superCE = axiom.getSuperClass();
        OWLClassExpression subCE = axiom.getSubClass();
        addFormula("forall X: (%s(X) => %s(X))", translate(subCE), translate(superCE));
        log.debug("SubclassOf axiom: %s\n", axiom);
    }

    @Override
    public void visit(OWLEquivalentClassesAxiom axiom) {
        List<OWLClassExpression> ces = axiom.classExpressions().collect(Collectors.toList());
        StringBuilder buf = new StringBuilder();
        Optional.of(ces.get(0)).ifPresent(ce -> buf.append(String.format("forall X: (%s(X)", translate(ce))));
        ces.stream().skip(1).forEach(ce -> buf.append(String.format(" <=> %s(X)", translate(ce))));
        buf.append(')');
        addFormula(buf.toString());
    }

    @Override
    public void doDefault(Object object) {
        log.error("%s\n", object);
    }
}
