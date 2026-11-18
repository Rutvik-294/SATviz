package satviz;

import java.util.*;

/**
 * Classic DPLL SAT solver that records its full execution as a replayable
 * list of search-tree Snapshots. Techniques: chronological backtracking,
 * unit propagation, pure-literal elimination, early termination.
 *
 * Tree nodes: id 1 is the root; each node carries the branch literal
 * (assigned when entering the node), its depth, and a status
 * (OPEN / SAT / UNSAT / PRUNED). Every solver event snapshots the whole
 * tree plus the current root-path assignment, so the GUI can time-travel.
 */
public final class DpllSolver {

    public static final int OPEN = 0, SAT = 1, UNSAT = 2, PRUNED = 3;

    /** One node of the recorded search tree.
     *  kind: 'D' = decision/assumption, 'P' = unit/pure propagation,
     *        'C' = conflict. */
    public static final class TNode {
        public final int id, parent, lit, depth;
        public final char kind;
        public int status = OPEN;
        TNode(int id, int parent, int lit, int depth, char kind) {
            this.id = id;
            this.parent = parent;
            this.lit = lit;
            this.depth = depth;
            this.kind = kind;
        }
    }

    /** Immutable snapshot: full tree + current path assignment + event info. */
    public static final class Snapshot {
        public final List<TNode> nodes;
        public final List<int[]> pathAssigns;   // {var, val(0/1)} along current path
        public final Set<Integer> pathNodes;    // ids of nodes on the root→current path
        public final Trace.Kind kind;
        public final String desc, note;
        public final int focusNode;             // tree node id of interest, 0 = none
        public final List<int[]> pureLits;      // {lit} found by pure-literal step
        Snapshot(List<TNode> nodes, List<int[]> pathAssigns, Set<Integer> pathNodes,
                 Trace.Kind kind, String desc, String note, int focusNode, List<int[]> pureLits) {
            this.nodes = nodes;
            this.pathAssigns = pathAssigns;
            this.pathNodes = pathNodes;
            this.kind = kind;
            this.desc = desc;
            this.note = note;
            this.focusNode = focusNode;
            this.pureLits = pureLits;
        }
    }

    private final int numVars;
    private final List<int[]> clauses = new ArrayList<>();     // unit-propagated working set
    private final boolean[] assign;
    private final boolean[] assigned;
    private int nodeId = 0;
    private boolean triviallyUnsat = false;
    private final List<TNode> tree = new ArrayList<>();
    private final Map<Integer, TNode> byId = new HashMap<>();
    private final List<TNode> path = new ArrayList<>();        // root-to-current stack

    /** Recorded execution: one Snapshot per solver event. */
    public final List<Snapshot> steps = new ArrayList<>();
    public final List<int[]> originalClauses = new ArrayList<>();

    TNode mkNode(int parent, int lit, int depth, char kind) {
        nodeId++;
        TNode n = new TNode(nodeId, parent, lit, depth, kind);
        byId.put(nodeId, n);
        tree.add(n);
        return n;
    }

    private List<int[]> pathAssigns() {
        List<int[]> out = new ArrayList<>();
        for (int v = 1; v <= numVars; v++) {
            if (assigned[v]) out.add(new int[]{v, assign[v] ? 1 : 0});
        }
        return out;
    }

    public DpllSolver(int numVars) {
        this.numVars = numVars;
        this.assign = new boolean[numVars + 1];
        this.assigned = new boolean[numVars + 1];
    }

    /** Add a clause; returns false on empty clause (trivially UNSAT). */
    public boolean addClause(int[] lits) {
        int[] c = lits.clone();
        Arrays.sort(c);
        int n = 0;
        for (int i = 0; i < c.length; i++) {
            if (i > 0 && c[i] == c[i - 1]) continue;
            if (i > 0 && c[i] == -c[i - 1]) return true;   // tautology: drop
            c[n++] = c[i];
        }
        if (n == 0) { triviallyUnsat = true; return false; }
        originalClauses.add(Arrays.copyOf(c, n));
        clauses.add(Arrays.copyOf(c, n));
        return true;
    }

    // ------------------------------------------------------------------
    public List<Snapshot> solve() {
        steps.clear();
        if (triviallyUnsat) {
            rec(Trace.Kind.UNSAT, "Empty clause in input — UNSATISFIABLE",
                    "An empty clause is false under every assignment.", 0, null);
            return steps;
        }
        rec(Trace.Kind.INIT, "Formula: " + clauses.size() + " clauses, "
                        + numVars + " variables",
                "DPLL explores the assignment tree chronologically: pick a "
                        + "variable, try True then False, backtrack on conflict.",
                0, null);
        boolean ok = dpll(0);
        if (ok) {
            rec(Trace.Kind.SAT, "SATISFIABLE — path found: " + pathAssignStr(),
                    "A full path with no empty clauses is a model.",
                    path.isEmpty() ? 0 : path.get(path.size() - 1).id, null);
        } else {
            rec(Trace.Kind.UNSAT, "Search tree exhausted — UNSATISFIABLE",
                    "Every branch was proven impossible: the formula has no model.",
                    0, null);
        }
        return steps;
    }

    /** Recursive DPLL. Returns true if SAT under the current path.
     *  Every event (assumption, unit-prop, pure-lit, conflict) becomes a
     *  node on the recorded tree, so the visualization shows the full
     *  derivation with conflicts hanging off the path. */
    private boolean dpll(int depth) {
        // ---- unit propagation ----
        while (true) {
            int unit = findUnit();
            if (unit == 0) break;
            int v = Math.abs(unit);
            TNode parent = path.isEmpty() ? null : path.get(path.size() - 1);
            if (assigned[v] && (assign[v] != (unit > 0))) {
                // conflicting unit: falsifies an existing path assignment
                TNode cnode = mkNode(parent == null ? 0 : parent.id, unit, depth, 'C');
                path.add(cnode);
                rec(Trace.Kind.CONFLICT,
                        "Unit " + litStr(unit) + " contradicts the path (x" + v
                                + " = " + (assign[v] ? "T" : "F") + ") — conflict",
                        "The forced literal " + litStr(unit) + " is false under an "
                                + "assignment already on the path: this branch fails.",
                        cnode.id, null);
                path.remove(path.size() - 1);
                return false;
            }
            if (!assigned[v]) {
                assign[v] = unit > 0;
                assigned[v] = true;
                TNode pnode = mkNode(parent == null ? 0 : parent.id, unit, depth, 'P');
                path.add(pnode);
                rec(Trace.Kind.PROPAGATE,
                        "Unit clause " + litStr(unit) + " → x" + v
                                + " = " + (assign[v] ? "T" : "F"),
                        "A clause reduced to a single literal forces its value: "
                                + "unit propagation.",
                        pnode.id, null);
                reduceClauses(v, assign[v]);
                if (hasEmpty()) {
                    TNode cnode = mkNode(pnode.id, unit, depth, 'C');
                    path.add(cnode);
                    rec(Trace.Kind.CONFLICT,
                            "Clause reduced to empty — conflict on x" + v,
                            "All literals of a clause are false: this branch is unsatisfiable.",
                            cnode.id, null);
                    path.remove(path.size() - 1);
                    undoAssign(v);
                    return false;
                }
            } else {
                reduceClauses(v, assign[v]);
                if (hasEmpty()) {
                    TNode cnode = mkNode(parent == null ? 0 : parent.id, unit, depth, 'C');
                    path.add(cnode);
                    rec(Trace.Kind.CONFLICT,
                            "Clause reduced to empty — conflict on x" + v,
                            "All literals of a clause are false: this branch is unsatisfiable.",
                            cnode.id, null);
                    path.remove(path.size() - 1);
                    return false;
                }
            }
        }

        // ---- pure literal elimination ----
        List<int[]> pures = findPures();
        if (!pures.isEmpty()) {
            TNode parent = path.isEmpty() ? null : path.get(path.size() - 1);
            List<TNode> pnodes = new ArrayList<>();
            for (int[] pv : pures) {
                int v = Math.abs(pv[0]);
                assign[v] = pv[0] > 0;
                assigned[v] = true;
                TNode pnode = mkNode(parent == null ? 0 : parent.id, pv[0], depth, 'P');
                if (parent != null) parent = pnode;   // chain pure-lit nodes
                pnodes.add(pnode);
            }
            path.addAll(pnodes);
            rec(Trace.Kind.PROPAGATE,
                    "Pure literals: " + pureListStr(pures) + " — assign freely",
                    "A literal that appears with only one polarity can always be "
                            + "set true: pure-literal elimination.",
                    pnodes.get(pnodes.size() - 1).id, pures);
            for (int[] pv : pures) reduceClauses(Math.abs(pv[0]), pv[0] > 0);
            if (hasEmpty()) {
                // cannot happen in theory (pures never falsify), guard anyway
                for (int[] pv : pures) undoAssign(Math.abs(pv[0]));
                for (int i = 0; i < pnodes.size(); i++) path.remove(path.size() - 1);
                return false;
            }
        }

        // ---- all clauses satisfied? ----
        if (clauses.isEmpty()) {
            // stamp the deepest path node SAT (the model leaf)
            TNode cur = path.isEmpty() ? null : path.get(path.size() - 1);
            if (cur != null) cur.status = SAT;
            return true;
        }

        // ---- branch ----
        int v = pickVar();
        for (int attempt = 0; attempt < 2; attempt++) {
            boolean val = attempt == 0;
            int lit = val ? v : -v;
            TNode parent = path.isEmpty() ? null : path.get(path.size() - 1);
            TNode node = mkNode(parent == null ? 0 : parent.id, lit, depth, 'D');
            path.add(node);
            rec(Trace.Kind.DECIDE,
                    "Assumption: x" + v + " = " + (val ? "T" : "F")
                            + "  (tree depth " + depth + ")",
                    "DPLL tries True first, then False; each assumption opens a "
                            + "new subtree with the clauses reduced accordingly.",
                    node.id, null);

            // reduce clauses under this branch (restorable)
            List<int[]> saved = snapshotClauses();
            boolean[] savedA = assign.clone();
            boolean[] savedAs = assigned.clone();
            assign[v] = val;
            assigned[v] = true;
            reduceClauses(v, val);
            if (hasEmpty()) {
                TNode cnode = mkNode(node.id, lit, depth, 'C');
                path.add(cnode);
                rec(Trace.Kind.CONFLICT,
                        "x" + v + " = " + (val ? "T" : "F") + " falsifies a clause — conflict",
                        "This assumption makes an entire clause false: the branch dies.",
                        cnode.id, null);
                path.remove(path.size() - 1);
                node.status = UNSAT;
                path.remove(path.size() - 1);
                restoreClauses(saved);
                System.arraycopy(savedA, 0, assign, 0, assign.length);
                System.arraycopy(savedAs, 0, assigned, 0, assigned.length);
                continue;
            }
            boolean ok = dpll(depth + 1);
            if (ok) {
                node.status = SAT;
                return true;   // keep assignments — the model lives in them
            }
            // child steps already recorded; restore for sibling
            path.remove(path.size() - 1);
            restoreClauses(saved);
            System.arraycopy(savedA, 0, assign, 0, assign.length);
            System.arraycopy(savedAs, 0, assigned, 0, assigned.length);
            node.status = UNSAT;
            rec(Trace.Kind.BACKJUMP,
                    "Subtree under x" + v + " = " + (val ? "T" : "F") + " is UNSAT — backtrack",
                    "Everything below this assumption was proven impossible: "
                            + "backtrack and try the sibling.",
                    node.id, null);
        }
        return false;
    }

    // ---- helpers ---------------------------------------------------------

    private int findUnit() {
        for (int[] c : clauses) if (c.length == 1) return c[0];
        return 0;
    }

    private boolean hasEmpty() {
        for (int[] c : clauses) if (c.length == 0) return true;
        return false;
    }

    /** Remove satisfied clauses and falsified literals for var=v set to val. */
    private void reduceClauses(int v, boolean val) {
        int lit = val ? v : -v;
        List<int[]> out = new ArrayList<>();
        for (int[] c : clauses) {
            boolean sat = false;
            List<Integer> rest = new ArrayList<>();
            for (int l : c) {
                if (l == lit) { sat = true; break; }
                if (l == -lit) continue;    // falsified literal removed
                rest.add(l);
            }
            if (!sat) out.add(rest.stream().mapToInt(Integer::intValue).toArray());
        }
        clauses.clear();
        clauses.addAll(out);
    }

    private List<int[]> snapshotClauses() {
        List<int[]> out = new ArrayList<>();
        for (int[] c : clauses) out.add(c.clone());
        return out;
    }

    private void restoreClauses(List<int[]> saved) {
        clauses.clear();
        for (int[] c : saved) clauses.add(c.clone());
    }

    /** Find literals appearing with only one polarity in the remaining clauses. */
    private List<int[]> findPures() {
        Map<Integer, Boolean> pol = new HashMap<>();
        Set<Integer> mixed = new HashSet<>();
        for (int[] c : clauses) {
            for (int l : c) {
                int v = Math.abs(l);
                if (mixed.contains(v)) continue;
                boolean pos = l > 0;
                Boolean prev = pol.get(v);
                if (prev == null) pol.put(v, pos);
                else if (prev != pos) { mixed.add(v); pol.remove(v); }
            }
        }
        List<int[]> out = new ArrayList<>();
        for (Map.Entry<Integer, Boolean> e : pol.entrySet()) {
            out.add(new int[]{e.getValue() ? e.getKey() : -e.getKey()});
        }
        return out;
    }

    /** Lowest-index unassigned var appearing in remaining clauses. */
    private int pickVar() {
        boolean[] seen = new boolean[numVars + 1];
        for (int[] c : clauses) for (int l : c) seen[Math.abs(l)] = true;
        for (int v = 1; v <= numVars; v++) if (seen[v]) return v;
        return 0;
    }

    private void undoAssign(int v) {
        assigned[v] = false;
    }

    private String litStr(int lit) {
        return (lit < 0 ? "¬" : "") + "x" + Math.abs(lit);
    }

    private String pureListStr(List<int[]> pures) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < pures.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(litStr(pures.get(i)[0]));
        }
        return sb.toString();
    }

    private String pathAssignStr() {
        StringBuilder sb = new StringBuilder();
        for (int[] a : pathAssigns()) {
            if (sb.length() > 0) sb.append(", ");
            sb.append("x").append(a[0]).append("=").append(a[1] == 1 ? "T" : "F");
        }
        return sb.toString();
    }

    private void rec(Trace.Kind kind, String desc, String note, int focusNode, List<int[]> pureLits) {
        if (steps.size() > 20000) return;
        List<TNode> copy = new ArrayList<>();
        for (TNode n : tree) {
            TNode c = new TNode(n.id, n.parent, n.lit, n.depth, n.kind);
            c.status = n.status;
            copy.add(c);
        }
        Set<Integer> pathIds = new LinkedHashSet<>();
        for (TNode n : path) pathIds.add(n.id);
        steps.add(new Snapshot(copy, pathAssigns(), pathIds, kind, desc, note, focusNode, pureLits));
    }

    /** Model read from the path + pure/unit assignments (SAT only). */
    public boolean[] model() {
        return assign.clone();
    }
}
