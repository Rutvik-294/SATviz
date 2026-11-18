package satviz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * CDCL SAT solver (MiniSat lineage) that records its full execution as a
 * replayable Trace. Techniques: two-watched-literal propagation, 1UIP
 * conflict analysis with self-subsumption minimization, non-chronological
 * backjumping, VSIDS with decay, phase saving, Luby restarts, LBD-based
 * learned clause reduction.
 */
public final class Solver {

    private final Trace trace = new Trace();

    // ---- clause database --------------------------------------------------
    private static final class Clause {
        final int[] lits;      // signed, 1-based vars; [0] and [1] are watched
        final boolean learnt;
        final int id;
        int lbd;
        boolean deleted;
        Clause(int[] lits, boolean learnt, int id) {
            this.lits = lits;
            this.learnt = learnt;
            this.id = id;
        }
    }

    private final List<Clause> clauses = new ArrayList<>();
    // watch index: lit>0 -> 2*lit, lit<0 -> 2*(-lit)+1
    private final List<List<Integer>> watches;
    private final List<Integer> emptyWl = new ArrayList<>();

    // ---- assignment state ---------------------------------------------------
    private final boolean[] assign;   // assign[v] = value of x_v
    private final boolean[] assigned;
    private final int[] level;        // decision level of assignment
    private final Clause[] reason;    // antecedent; null for decisions/level-0
    private final List<Integer> trail = new ArrayList<>();
    private int[] trailLimit = new int[64];
    private int dl = 0;               // current decision level
    private int qhead = 0;

    // ---- search heuristics ---------------------------------------------------
    private final double[] activity;
    private double varInc = 1.0;
    private final boolean[] phase;
    private long conflicts = 0, decisions = 0, propagations = 0;
    private static final double VAR_DECAY = 0.95;
    private long conflictsSinceRestart = 0;
    private int restartCount = 0;
    private long restartLimit;
    private long reduceLimit = 2000;
    private static final int GLUE_KEEP = 2;   // LBD <= 2 kept forever

    private final int numVars;
    private boolean[] model;          // set on SAT
    private boolean triviallyUnsat = false;

    public Solver(int numVars) {
        this.numVars = numVars;
        this.assign = new boolean[numVars + 1];
        this.assigned = new boolean[numVars + 1];
        this.level = new int[numVars + 1];
        this.reason = new Clause[numVars + 1];
        this.activity = new double[numVars + 1];
        this.phase = new boolean[numVars + 1];
        Arrays.fill(phase, true);
        this.watches = new ArrayList<>(2 * numVars + 2);
        for (int i = 0; i < 2 * numVars + 2; i++) watches.add(new ArrayList<>());
        this.restartLimit = lubyNext();
    }

    /** Add a clause; returns false on trivially UNSAT (empty or contradictory units). */
    public boolean addClause(int[] lits) {
        int[] c = lits.clone();
        Arrays.sort(c);
        int n = 0;
        for (int i = 0; i < c.length; i++) {
            if (i > 0 && c[i] == c[i - 1]) continue;
            if (i > 0 && c[i] == -c[i - 1]) return true; // tautology
            c[n++] = c[i];
        }
        if (n == 0) return false;
        Clause cl = new Clause(Arrays.copyOf(c, n), false, clauses.size());
        clauses.add(cl);
        if (n == 1) {
            if (!enqueue(cl.lits[0], null)) { triviallyUnsat = true; return false; }
        } else {
            for (int i = 0; i < 2; i++) watch(cl.lits[i]).add(cl.id);
        }
        return true;
    }

    private List<Integer> watch(int lit) {
        int idx = lit > 0 ? 2 * lit : 2 * (-lit) + 1;
        if (idx >= watches.size()) return emptyWl;
        return watches.get(idx);
    }

    private boolean litSat(int lit) {
        if (!assigned[Math.abs(lit)]) return false;
        boolean v = assign[Math.abs(lit)];
        return lit > 0 ? v : !v;
    }

    private boolean litFalse(int lit) {
        return assigned[Math.abs(lit)] && !litSat(lit);
    }

    /** Enqueue an assignment with optional reason; returns false on conflict. */
    private boolean enqueue(int lit, Clause why) {
        int v = Math.abs(lit);
        boolean val = lit > 0;
        if (assigned[v]) return litSat(lit);
        assigned[v] = true;
        assign[v] = val;
        level[v] = dl;
        reason[v] = why;
        trail.add(v);
        bump(v);
        return true;
    }

    // ------------------------------------------------------------------
    public Trace solve() {
        recordInit();
        if (triviallyUnsat) {
            recordUnsat(-2);
            return trace;
        }
        Clause c0 = propagateFull(null);
        if (c0 != null) {
            recordUnsat(c0.id);
            return trace;
        }
        while (true) {
            Clause confl = propagateFull(null);
            if (confl != null) {
                if (dl == 0) {
                    recordUnsat(confl.id);
                    return trace;
                }
                conflicts++;
                conflictsSinceRestart++;
                decay();
                analyze(confl);
            } else {
                if (conflictsSinceRestart >= restartLimit) {
                    conflictsSinceRestart = 0;
                    restartCount++;
                    restartLimit = lubyNext();
                    cancelUntil(0);
                    record(Trace.Kind.RESTART,
                            "Restart #" + restartCount + " — back to level 0",
                            "Luby-scheduled restarts escape unlucky subtrees; "
                                    + "learned clauses and VSIDS activity persist.",
                            0, null, null, -1);
                    continue;
                }
                if (conflicts >= reduceLimit) reduceDB();
                int v = pickBranch();
                if (v == 0) {
                    model = assign.clone();
                    recordSat();
                    return trace;
                }
                decisions++;
                dl++;
                if (dl >= trailLimit.length) {
                    trailLimit = Arrays.copyOf(trailLimit, trailLimit.length * 2);
                }
                trailLimit[dl] = trail.size();
                int lit = phase[v] ? v : -v;
                enqueue(lit, null);
                record(Trace.Kind.DECIDE,
                        "Decision: x" + v + " = " + (lit > 0 ? "T" : "F")
                                + "  (level " + dl + ")",
                        "VSIDS picks the highest-activity unassigned variable; "
                                + "the saved phase is tried first.",
                        v, null, null, -1);
            }
        }
    }

    public boolean[] model() { return model; }

    // ------------------------------------------------------------------
    /** Propagate to fixpoint. Returns conflict clause or null. */
    private Clause propagateFull(Clause skip) {
        while (qhead < trail.size()) {
            int v = trail.get(qhead++);
            int flit = assign[v] ? -v : v;   // literal that just became false
            List<Integer> wl = watch(flit);
            int i = 0, j = 0;
            Clause conflictClause = null;
            while (i < wl.size()) {
                int cid = wl.get(i++);
                Clause c = clauses.get(cid);
                if (c.deleted) continue;
                // make c.lits[1] the falsified literal
                if (c.lits[1] != flit) {
                    int tmp = c.lits[0]; c.lits[0] = c.lits[1]; c.lits[1] = tmp;
                }
                int first = c.lits[0];
                if (first != flit && litSat(first)) {
                    wl.set(j++, cid);
                    continue;
                }
                // search for a non-false replacement watch
                boolean moved = false;
                for (int k = 2; k < c.lits.length; k++) {
                    if (!litFalse(c.lits[k])) {
                        c.lits[1] = c.lits[k];
                        c.lits[k] = flit;
                        watch(c.lits[1]).add(cid);
                        moved = true;
                        break;
                    }
                }
                if (moved) continue;   // dropped from this watch list
                if (litFalse(first)) {
                    wl.set(j++, cid);
                    conflictClause = c;
                    qhead = trail.size();
                    // keep the rest of the list as-is
                    while (i < wl.size()) wl.set(j++, wl.get(i++));
                    break;
                }
                // unit: first is the only non-false literal
                propagations++;
                enqueue(first, c);
                wl.set(j++, cid);
            }
            wl.subList(j, wl.size()).clear();
            if (conflictClause != null) return conflictClause;
        }
        return null;
    }

    // ------------------------------------------------------------------
    /** 1UIP conflict analysis: learn clause, backjump, assert UIP. */
    private void analyze(Clause confl) {
        boolean[] seen = new boolean[numVars + 1];
        List<Integer> learned = new ArrayList<>();
        List<Integer> cur = new ArrayList<>();
        for (int l : confl.lits) cur.add(l);
        record(Trace.Kind.CONFLICT,
                "CONFLICT in " + clauseStr(confl.lits) + "  (clause #" + confl.id + ")",
                "Every literal is false under the current assignment. Begin "
                        + "resolving backward through the trail to learn why.",
                Math.abs(confl.lits[0]), cur, null, confl.id);

        int counter = 0;   // unresolved literals at the current decision level
        int p = 0;
        int skipVar = 0;   // previous pivot: its own literal is skipped when marking
        Clause sel = confl;
        int idx = trail.size() - 1;

        // MiniSat-style do-while: the pivot whose resolution drives counter
        // to 0 is the 1UIP; its reason clause is never resolved in.
        do {
            for (int l : sel.lits) {
                int v = Math.abs(l);
                if (v == skipVar || seen[v] || level[v] == 0) continue;
                seen[v] = true;
                bump(v);
                if (level[v] == dl) counter++;
                else learned.add(l);
            }
            while (idx > 0 && !seen[trail.get(idx)]) idx--;
            p = trail.get(idx);
            sel = reason[p];
            counter--;
            idx--;
            seen[p] = false;   // pivot resolved — must be re-seenable via other reasons
            skipVar = p;       // ...but not by its own reason clause
            if (counter > 0) {
                if (sel == null) break;   // safety: decision reached with unresolved lits
                // record intermediate resolve state (clause as it stands)
                cur = new ArrayList<>(learned);
                for (int l : sel.lits) {
                    int v = Math.abs(l);
                    if (v == p || seen[v] || level[v] == 0) continue;
                    cur.add(l);
                }
                record(Trace.Kind.RESOLVE,
                        "Resolve on x" + p + " (set by " + clauseStr(sel.lits) + ")",
                        "x" + p + " was propagated, so its reason clause explains it: "
                                + "resolve it away and continue.",
                        p, cur, null, sel.id);
            }
        } while (counter > 0);

        // the learned literal is the negation of the UIP's ASSIGNED value
        // (a decision set to False yields +p, not -p)
        int uipLit = assign[p] ? -p : p;
        learned.add(uipLit);
        learned.remove(Integer.valueOf(uipLit));
        learned.add(0, uipLit);
        minimize(learned, seen);

        int[] arr = new int[learned.size()];
        for (int i = 0; i < arr.length; i++) arr[i] = learned.get(i);

        int bj = 0;
        for (int i = 1; i < arr.length; i++) {
            int lv = level[Math.abs(arr[i])];
            if (lv > bj) bj = lv;
        }

        Clause learnt = new Clause(arr, true, clauses.size());
        learnt.lbd = computeLbd(arr);
        clauses.add(learnt);
        if (arr.length > 1) {
            // put the literal with the highest level at position 1
            // (so backtracking unbinds it first); UIP neg stays at 0
            int best = 1;
            for (int i = 2; i < arr.length; i++) {
                if (level[Math.abs(arr[i])] > level[Math.abs(arr[best])]) best = i;
            }
            int t = arr[1]; arr[1] = arr[best]; arr[best] = t;
            learnt.lits[1] = arr[1];
            learnt.lits[best] = arr[best];
            watch(learnt.lits[0]).add(learnt.id);
            watch(learnt.lits[1]).add(learnt.id);
        }

        record(Trace.Kind.LEARN,
                "Learned (1UIP): " + clauseStr(arr) + "  →  backjump to level " + bj,
                "Resolving stops when exactly ONE literal of the current level "
                        + "remains — the First Unique Implication Point.",
                Math.abs(arr[0]), new ArrayList<>(learned), null, learnt.id);

        cancelUntil(bj);
        record(Trace.Kind.BACKJUMP,
                "Backjump: level " + dl + " → " + bj,
                "Non-chronological backtracking: intermediate levels couldn't "
                        + "have caused the conflict, so they're skipped entirely.",
                0, null, null, -1);

        // assert the UIP (works for unit and non-unit learned clauses)
        enqueue(arr[0], arr.length > 1 ? learnt : null);
        record(Trace.Kind.ASSERT,
                "Assert x" + Math.abs(arr[0]) + " = " + (arr[0] > 0 ? "T" : "F")
                        + " (the learned clause is unit)",
                "The UIP's negation is forced at level " + bj + ".",
                Math.abs(arr[0]), new ArrayList<>(learned), null, learnt.id);
    }

    /** Remove literals implied by the rest of the clause (self-subsumption).
     *  Conservative form: a literal l is redundant only if every other literal
     *  of its reason clause is *literally present* in the learned clause
     *  (complemented — they are all falsified, so membership means the same
     *  var is being claimed in its falsified polarity). */
    private void minimize(List<Integer> learned, boolean[] seen) {
        outer:
        for (int i = learned.size() - 1; i >= 1; i--) {
            int l = learned.get(i);
            Clause r = reason[Math.abs(l)];
            if (r == null) continue;
            for (int rl : r.lits) {
                if (Math.abs(rl) == Math.abs(l)) continue;
                if (level[Math.abs(rl)] == 0) continue;   // level-0 facts are free
                if (!learned.contains(-rl)) continue outer;
            }
            learned.remove(i);
        }
    }

    private int computeLbd(int[] lits) {
        int n = 0;
        int[] seenLv = new int[lits.length];
        for (int l : lits) {
            int lv = level[Math.abs(l)];
            boolean dup = false;
            for (int i = 0; i < n; i++) if (seenLv[i] == lv) { dup = true; break; }
            if (!dup) seenLv[n++] = lv;
        }
        return n;
    }

    // ------------------------------------------------------------------
    private int pickBranch() {
        // linear scan for highest-activity unassigned var (robust and simple;
        // VSIDS activity ordering is what matters, not micro-speed)
        int best = 0;
        for (int v = 1; v <= numVars; v++) {
            if (assigned[v]) continue;
            if (best == 0 || activity[v] > activity[best]) best = v;
        }
        return best;
    }

    private void cancelUntil(int lvl) {
        while (dl > lvl) {
            int lim = trailLimit[dl];
            while (trail.size() > lim) {
                int v = trail.remove(trail.size() - 1);
                phase[v] = assign[v];     // phase saving
                assigned[v] = false;
            }
            dl--;
        }
        qhead = Math.min(qhead, trail.size());
    }

    private void bump(int v) {
        activity[v] += varInc;
        if (activity[v] > 1e100) rescale();
    }

    private void decay() {
        varInc /= VAR_DECAY;   // geometric activity growth = geometric decay
    }

    private void rescale() {
        for (int v = 1; v <= numVars; v++) activity[v] *= 1e-100;
        varInc *= 1e-100;
    }

    private long lubyNext() {
        // Standard Luby: 1,1,2,1,1,2,4,1,1,2,4,8,... (i is 1-based run index)
        return lubyClassic(restartCount + 1) * 100;
    }

    private long lubyClassic(int i) {
        // Luby: 1,1,2,1,1,2,4,1,1,2,4,8,... (i is 1-based)
        while (true) {
            int p = 1;
            while (p * 2 - 1 <= i) p *= 2;
            if (p - 1 == i) return p / 2;
            i = i - (p - 1);
        }
    }

    private void reduceDB() {
        List<Clause> learnts = new ArrayList<>();
        for (Clause c : clauses) {
            if (c.learnt && !c.deleted) learnts.add(c);
        }
        learnts.sort((a, b) -> Integer.compare(b.lbd, a.lbd));
        int target = learnts.size() / 2;
        int removed = 0;
        for (Clause c : learnts) {
            if (removed >= target) break;
            if (c.lbd <= GLUE_KEEP) continue;
            boolean used = false;
            for (int v : trail) if (reason[v] == c) { used = true; break; }
            if (used) continue;
            c.deleted = true;
            for (int l : c.lits) watch(l).remove(Integer.valueOf(c.id));
            removed++;
        }
        reduceLimit += 2000;
        record(Trace.Kind.REDUCE,
                "DB reduction: deleted " + removed + " high-LBD learned clauses",
                "Learned clauses with low LBD (glue) are kept; the rest are "
                        + "half-deleted when the database doubles.",
                0, null, null, -1);
    }

    // ------------------------------------------------------------------
    // trace helpers

    private List<int[]> trailRows() {
        List<int[]> rows = new ArrayList<>();
        for (int v : trail) {
            rows.add(new int[]{v, assign[v] ? 1 : 0,
                    reason[v] == null ? -1 : reason[v].id, level[v]});
        }
        return rows;
    }

    private List<int[]> learnedRows() {
        List<int[]> rows = new ArrayList<>();
        for (Clause c : clauses) {
            if (c.deleted) continue;
            // row = [clauseId, isLearnt, lits...] — the GUI reads this format
            int[] row = new int[c.lits.length + 2];
            row[0] = c.id;
            row[1] = c.learnt ? 1 : 0;
            System.arraycopy(c.lits, 0, row, 2, c.lits.length);
            rows.add(row);
        }
        return rows;
    }

    private List<Trace.Edge> edgesNow() {
        List<Trace.Edge> edges = new ArrayList<>();
        for (int v : trail) {
            Clause r = reason[v];
            if (r == null) continue;
            for (int l : r.lits) {
                int w = Math.abs(l);
                if (w != v && assigned[w]) edges.add(new Trace.Edge(w, v, r.id));
            }
        }
        return edges;
    }

    private String clauseStr(int[] lits) {
        if (lits.length == 0) return "⊥";
        StringBuilder sb = new StringBuilder("(");
        for (int i = 0; i < lits.length; i++) {
            if (i > 0) sb.append(" ∨ ");
            int l = lits[i];
            sb.append(l < 0 ? "¬" : "").append("x").append(Math.abs(l));
        }
        return sb.append(")").toString();
    }

    private void recordInit() {
        trace.snapshot(Trace.Kind.INIT,
                "Formula: " + clauses.size() + " clauses, " + numVars + " variables",
                "CDCL starts with nothing assigned; every conflict teaches it "
                        + "a new clause so it never makes the same mistake twice.",
                new boolean[numVars + 1], List.of(), List.of(), List.of(),
                0, -1, null, 0, List.of());
    }

    private void recordUnsat(int conflId) {
        trace.snapshot(Trace.Kind.UNSAT,
                conflId < 0
                        ? "Empty clause in input — UNSATISFIABLE"
                        : "Conflict at decision level 0 — UNSATISFIABLE",
                "A level-0 conflict holds under every possible assignment, "
                        + "so the formula is proven UNSAT.",
                new boolean[numVars + 1], List.of(), List.of(), List.of(),
                0, conflId, null, 0, List.of());
    }

    private void recordSat() {
        trace.snapshot(Trace.Kind.SAT,
                "All variables assigned, no conflicts — SATISFIABLE!  "
                        + "(conflicts=" + conflicts + " decisions=" + decisions
                        + " propagations=" + propagations + ")",
                "Total work: " + trace.steps.size() + " recorded steps.",
                assign, trailRows(), learnedRows(), edgesNow(), dl,
                -1, null, 0, List.of());
    }

    private void record(Trace.Kind kind, String desc, String note,
                        int focusVar, List<Integer> learningClause,
                        List<Integer> touched, int highlightClause) {
        if (trace.steps.size() > 20000) return;   // hard cap: memory guard for big runs
        trace.snapshot(kind, desc, note, assign, trailRows(), learnedRows(),
                edgesNow(), dl, highlightClause, learningClause, focusVar, touched);
    }
}
