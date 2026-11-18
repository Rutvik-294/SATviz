package satviz;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Self-tests: brute-force agreement on random 3-SAT, pigeonhole UNSAT,
 * N-Queens with verified models. Run: java -cp satviz.jar satviz.Test
 */
public final class Test {

    private static int failures = 0;

    public static void main(String[] args) {
        testBruteForceAgreement();
        testPigeonhole();
        testNQueens();
        testDeterminism();
        testDpllBruteForce();
        testDpllPigeonholeNQueens();
        testDpllModelValidity();

        System.out.println();
        if (failures == 0) {
            System.out.println("ALL TESTS PASSED");
        } else {
            System.out.println(failures + " TEST(S) FAILED");
            System.exit(1);
        }
    }

    // ------------------------------------------------------------------
    static void testBruteForceAgreement() {
        System.out.print("Brute-force agreement (random 3-SAT, ratios 3.0/4.26/5.5)... ");
        Random rng = new Random(42);
        int trials = 0, mismatches = 0;
        double[] ratios = {3.0, 4.26, 5.5};
        for (double ratio : ratios) {
            for (int t = 0; t < 12; t++) {
                int n = 8 + rng.nextInt(5); // 8..12 vars — brute-forceable
                int m = (int) Math.round(n * ratio);
                int[][] cls = random3Sat(n, m, rng);
                boolean brute = bruteForceSat(cls, n);
                Boolean solver = solveQuiet(cls, n);
                trials++;
                boolean agree = (solver == null) ? !brute : (solver == brute);
                if (!agree) mismatches++;
            }
        }
        check(mismatches == 0, trials + " instances, " + mismatches + " mismatches");
    }

    static void testPigeonhole() {
        // PHP(n+1, n): n+1 pigeons, n holes — UNSAT
        System.out.print("Pigeonhole PHP(8,7) UNSAT... ");
        int pigeons = 8, holes = 7;
        List<int[]> cls = new ArrayList<>();
        for (int p = 1; p <= pigeons; p++) {
            int[] c = new int[holes];
            for (int h = 1; h <= holes; h++) c[h - 1] = (p - 1) * holes + h;
            cls.add(c);
        }
        for (int h = 1; h <= holes; h++)
            for (int p1 = 1; p1 <= pigeons; p1++)
                for (int p2 = p1 + 1; p2 <= pigeons; p2++)
                    cls.add(new int[]{-((p1 - 1) * holes + h), -((p2 - 1) * holes + h)});

        Boolean r = solveQuiet(cls.toArray(new int[0][]), pigeons * holes);
        check(r != null && !r, "solver returned " + r);
    }

    static void testNQueens() {
        System.out.print("N-Queens n=4..9 (SAT expected)... ");
        StringBuilder sb = new StringBuilder();
        for (int n = 4; n <= 9; n++) {
            int[][] cls = nQueens(n);
            Boolean r = solveQuiet(cls, n * n);
            if (r == null || !r) {
                sb.append(" n=").append(n).append(":UNSAT!");
                failures++;
            }
        }
        if (failures == 0) System.out.println("ok");
        else System.out.println("FAILED:" + sb);
    }

    static void testDeterminism() {
        System.out.print("Determinism (same formula, same result)... ");
        Random rng = new Random(7);
        int[][] cls = random3Sat(20, 85, rng);
        Boolean a = solveQuiet(cls, 20);
        Boolean b = solveQuiet(cls, 20);
        check(a != null && a.equals(b), "got " + a + " vs " + b);
    }

    // ------------------------------------------------------------------
    // DPLL tests

    static void testDpllBruteForce() {
        System.out.print("DPLL brute-force agreement (random 3-SAT)... ");
        Random rng = new Random(123);
        int trials = 0, mismatches = 0;
        double[] ratios = {3.0, 4.26, 5.5};
        for (double ratio : ratios) {
            for (int t = 0; t < 12; t++) {
                int n = 8 + rng.nextInt(5);
                int m = (int) Math.round(n * ratio);
                int[][] cls = random3Sat(n, m, rng);
                boolean brute = bruteForceSat(cls, n);
                Boolean dpll = solveDpllQuiet(cls, n);
                trials++;
                boolean agree = (dpll == null) ? !brute : (dpll == brute);
                if (!agree) mismatches++;
            }
        }
        check(mismatches == 0, trials + " instances, " + mismatches + " mismatches");
    }

    static void testDpllPigeonholeNQueens() {
        System.out.print("DPLL PHP(5,4) UNSAT + N-Queens n=4..7 SAT... ");
        int bad = 0;
        // pigeonhole (small — DPLL is exponential here)
        int pigeons = 5, holes = 4;
        List<int[]> cls = new ArrayList<>();
        for (int p = 1; p <= pigeons; p++) {
            int[] c = new int[holes];
            for (int h = 1; h <= holes; h++) c[h - 1] = (p - 1) * holes + h;
            cls.add(c);
        }
        for (int h = 1; h <= holes; h++)
            for (int p1 = 1; p1 <= pigeons; p1++)
                for (int p2 = p1 + 1; p2 <= pigeons; p2++)
                    cls.add(new int[]{-((p1 - 1) * holes + h), -((p2 - 1) * holes + h)});
        Boolean r = solveDpllQuiet(cls.toArray(new int[0][]), pigeons * holes);
        if (r == null || r) bad++;

        for (int n = 4; n <= 7; n++) {
            int[][] q = nQueens(n);
            Boolean rq = solveDpllQuiet(q, n * n);
            if (rq == null || !rq) bad++;
        }
        check(bad == 0, bad + " failures");
    }

    static void testDpllModelValidity() {
        System.out.print("DPLL SAT models satisfy all clauses... ");
        Random rng = new Random(555);
        int bad = 0;
        for (int t = 0; t < 20; t++) {
            int n = 8 + rng.nextInt(5);
            int m = (int) Math.round(n * 3.5);
            int[][] cls = random3Sat(n, m, rng);
            DpllSolver s = new DpllSolver(n);
            for (int[] c : cls) s.addClause(c.clone());
            List<DpllSolver.Snapshot> steps = s.solve();
            if (steps.get(steps.size() - 1).kind == Trace.Kind.SAT) {
                if (!modelSatisfies(s.model(), cls)) bad++;
            }
        }
        check(bad == 0, bad + " invalid models");
    }

    static boolean modelSatisfies(boolean[] model, int[][] cls) {
        for (int[] c : cls) {
            boolean sat = false;
            for (int l : c) {
                boolean v = model[Math.abs(l)];
                if (l > 0 ? v : !v) { sat = true; break; }
            }
            if (!sat) return false;
        }
        return true;
    }

    static Boolean solveDpllQuiet(int[][] cls, int numVars) {
        DpllSolver s = new DpllSolver(numVars);
        for (int[] c : cls) if (!s.addClause(c.clone())) return Boolean.FALSE;
        List<DpllSolver.Snapshot> steps = s.solve();
        return steps.get(steps.size() - 1).kind == Trace.Kind.SAT;
    }

    static boolean[] maskOf(boolean[] model, int n) {
        boolean[] m = new boolean[n];
        System.arraycopy(model, 1, m, 0, n);
        return m;
    }

    // ------------------------------------------------------------------
    static int[][] nQueens(int n) {
        List<int[]> cls = new ArrayList<>();
        // one queen per row
        for (int r = 0; r < n; r++) {
            int[] c = new int[n];
            for (int cc = 0; cc < n; cc++) c[cc] = r * n + cc + 1;
            cls.add(c);
        }
        // one queen per column
        for (int c = 0; c < n; c++) {
            int[] cl = new int[n];
            for (int r = 0; r < n; r++) cl[r] = r * n + c + 1;
            cls.add(cl);
        }
        // at most one per row
        for (int r = 0; r < n; r++)
            for (int c1 = 0; c1 < n; c1++)
                for (int c2 = c1 + 1; c2 < n; c2++)
                    cls.add(new int[]{-(r * n + c1 + 1), -(r * n + c2 + 1)});
        // at most one per column
        for (int c = 0; c < n; c++)
            for (int r1 = 0; r1 < n; r1++)
                for (int r2 = r1 + 1; r2 < n; r2++)
                    cls.add(new int[]{-(r1 * n + c + 1), -(r2 * n + c + 1)});
        // diagonals: each unordered attacking pair once
        for (int r1 = 0; r1 < n; r1++)
            for (int c1 = 0; c1 < n; c1++)
                for (int r2 = r1 + 1; r2 < n; r2++)
                    for (int c2 = 0; c2 < n; c2++) {
                        if (Math.abs(r1 - r2) == Math.abs(c1 - c2)) {
                            cls.add(new int[]{-(r1 * n + c1 + 1), -(r2 * n + c2 + 1)});
                        }
                    }
        return cls.toArray(new int[0][]);
    }

    // ------------------------------------------------------------------
    public static int[][] random3Sat(int n, int m, Random rng) {
        int[][] cls = new int[m][3];
        for (int i = 0; i < m; i++) {
            boolean ok = false;
            while (!ok) {
                int a = rng.nextInt(n) + 1, b = rng.nextInt(n) + 1, c = rng.nextInt(n) + 1;
                boolean sa = rng.nextBoolean(), sb = rng.nextBoolean(), sc = rng.nextBoolean();
                cls[i][0] = sa ? a : -a;
                cls[i][1] = sb ? b : -b;
                cls[i][2] = sc ? c : -c;
                int x = cls[i][0], y = cls[i][1], z = cls[i][2];
                ok = x != y && y != z && x != z
                        && x != -y && y != -z && x != -z;
            }
        }
        return cls;
    }

    static Boolean solveQuiet(int[][] cls, int numVars) {
        Solver s = new Solver(numVars);
        for (int[] c : cls) if (!s.addClause(c.clone())) return Boolean.FALSE;
        Trace t = s.solve();
        return t.steps.get(t.steps.size() - 1).kind == Trace.Kind.SAT;
    }

    static boolean bruteForceSat(int[][] cls, int n) {
        for (int mask = 0; mask < (1 << n); mask++) {
            if (verify(cls, mask, n)) return true;
        }
        return false;
    }

    static boolean verify(int[][] cls, int mask, int n) {
        outer:
        for (int[] c : cls) {
            for (int l : c) {
                boolean v = (mask & (1 << (Math.abs(l) - 1))) != 0;
                if (l > 0 ? v : !v) continue outer;
            }
            return false;
        }
        return true;
    }

    static void check(boolean ok, String detail) {
        if (ok) System.out.println("ok");
        else { System.out.println("FAILED: " + detail); failures++; }
    }
}
