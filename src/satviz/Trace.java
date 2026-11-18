package satviz;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * Fully-recorded solver execution. Every event snapshots the complete
 * solver state (assignment, trail, learned DB, implication graph edges),
 * so the GUI can time-travel to any point.
 */
public final class Trace {

    public enum Kind {
        INIT("init"), DECIDE("decide"), PROPAGATE("propagate"),
        CONFLICT("conflict"), RESOLVE("resolve"), LEARN("learn"),
        BACKJUMP("backjump"), ASSERT("assert"), RESTART("restart"),
        REDUCE("reduce"), SAT("sat"), UNSAT("unsat");

        public final String label;
        Kind(String label) { this.label = label; }
    }

    /** One implication-graph edge: reason var -> implied var. */
    public record Edge(int from, int to, int clauseId) {}

    /** Immutable snapshot of solver state at one step. */
    public static final class Step {
        public final Kind kind;
        public final String desc;          // human explanation
        public final String note;          // extra didactic line
        public final boolean[] assign;     // null = unassigned
        public final List<int[]> trail;    // {var, value(0/1), reasonClauseId, level}
        public final List<int[]> learned;  // learned clauses so far (as signed literals)
        public final List<Edge> edges;     // implication graph edges now
        public final int decisionLevel;
        public final int highlightClause;  // clause id to flash, -1 none
        public final List<Integer> learningClause; // clause being built (resolve steps)
        public final int focusVar;         // variable of interest, 0 = none
        public final List<Integer> touchedClause; // clause ids to color

        Step(Kind kind, String desc, String note, boolean[] assign,
             List<int[]> trail, List<int[]> learned, List<Edge> edges,
             int decisionLevel, int highlightClause, List<Integer> learningClause,
             int focusVar, List<Integer> touchedClause) {
            this.kind = kind;
            this.desc = desc;
            this.note = note;
            this.assign = assign.clone();
            this.trail = deepCopy(trail);
            this.learned = deepCopy(learned);
            this.edges = List.copyOf(edges);
            this.decisionLevel = decisionLevel;
            this.highlightClause = highlightClause;
            this.learningClause = learningClause == null ? null : List.copyOf(learningClause);
            this.focusVar = focusVar;
            this.touchedClause = touchedClause == null ? List.of() : List.copyOf(touchedClause);
        }

        private static List<int[]> deepCopy(List<int[]> src) {
            List<int[]> out = new ArrayList<>(src.size());
            for (int[] r : src) out.add(r.clone());
            return Collections.unmodifiableList(out);
        }
    }

    public final List<Step> steps = new ArrayList<>();
    public final List<int[]> originalClauses = new ArrayList<>(); // signed lits

    void snapshot(Kind kind, String desc, String note, boolean[] assign,
                  List<int[]> trail, List<int[]> learned, List<Edge> edges,
                  int dl, int highlightClause, List<Integer> learningClause,
                  int focusVar, List<Integer> touchedClause) {
        steps.add(new Step(kind, desc, note, assign, trail, learned, edges,
                dl, highlightClause, learningClause, focusVar, touchedClause));
    }
}
