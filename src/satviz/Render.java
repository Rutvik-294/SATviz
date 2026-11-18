package satviz;

import java.awt.image.BufferedImage;
import java.io.File;
import java.nio.file.*;
import java.util.*;
import javax.imageio.ImageIO;

/**
 * Headless PNG export of a demo trace — used to verify the graph
 * rendering without a display: java -jar satviz.jar --render DIR
 */
public final class Render {

    public static void render(String outDir) throws Exception {
        Files.createDirectories(Path.of(outDir));

        // chain preset: decision → propagation chain → conflict → learn → assert
        List<int[]> cls = List.of(
                new int[]{1, 2}, new int[]{-1, 3}, new int[]{-1, 4},
                new int[]{-3, -4}, new int[]{-2, 5}, new int[]{-2, 6},
                new int[]{-5, -6});
        Solver s = new Solver(6);
        for (int[] c : cls) s.addClause(c.clone());
        Trace trace = s.solve();
        int conI = -1, lrnI = -1, asrI = -1;
        for (int i = 0; i < trace.steps.size(); i++) {
            Trace.Kind k = trace.steps.get(i).kind;
            if (k == Trace.Kind.CONFLICT && conI < 0) conI = i;
            if (k == Trace.Kind.LEARN && lrnI < 0) lrnI = i;
            if (k == Trace.Kind.ASSERT && asrI < 0) asrI = i;
        }
        exportTrace(trace, "chain", outDir, new int[]{1, conI, lrnI, asrI});

        // pigeonhole for a conflict-heavy graph
        int pigeons = 3, holes = 2;
        List<int[]> php = new ArrayList<>();
        for (int p = 1; p <= pigeons; p++) {
            int[] c = new int[holes];
            for (int h = 1; h <= holes; h++) c[h - 1] = (p - 1) * holes + h;
            php.add(c);
        }
        for (int h = 1; h <= holes; h++)
            for (int p1 = 1; p1 <= pigeons; p1++)
                for (int p2 = p1 + 1; p2 <= pigeons; p2++)
                    php.add(new int[]{-((p1 - 1) * holes + h), -((p2 - 1) * holes + h)});
        Solver s2 = new Solver(pigeons * holes);
        for (int[] c : php) s2.addClause(c.clone());
        Trace t2 = s2.solve();
        // pick the interesting moments: conflict, mid-resolution, learn, assert
        int conflict = -1, learn = -1, assertI = -1;
        for (int i = 0; i < t2.steps.size(); i++) {
            Trace.Kind k = t2.steps.get(i).kind;
            if (k == Trace.Kind.CONFLICT && conflict < 0) conflict = i;
            if (k == Trace.Kind.LEARN && learn < 0) learn = i;
            if (k == Trace.Kind.ASSERT && assertI < 0) assertI = i;
        }
        exportTrace(t2, "php32", outDir, new int[]{1, conflict, learn, assertI});

        // ---- DPLL search tree (pigeonhole: real branching) ---------------
        int dp = 4, dh = 3;
        List<int[]> dcls = new ArrayList<>();
        for (int p = 1; p <= dp; p++) {
            int[] c = new int[dh];
            for (int h = 1; h <= dh; h++) c[h - 1] = (p - 1) * dh + h;
            dcls.add(c);
        }
        for (int h = 1; h <= dh; h++)
            for (int p1 = 1; p1 <= dp; p1++)
                for (int p2 = p1 + 1; p2 <= dp; p2++)
                    dcls.add(new int[]{-((p1 - 1) * dh + h), -((p2 - 1) * dh + h)});
        DpllSolver d = new DpllSolver(dp * dh);
        for (int[] c : dcls) d.addClause(c.clone());
        List<DpllSolver.Snapshot> dsteps = d.solve();
        int[] picks = {0, Math.min(2, dsteps.size() - 1), dsteps.size() / 2, dsteps.size() - 1};
        java.util.LinkedHashSet<Integer> pickSet = new java.util.LinkedHashSet<>();
        for (int p : picks) pickSet.add(Math.max(0, Math.min(dsteps.size() - 1, p)));
        for (int idx : pickSet) {
            DpllSolver.Snapshot cur = dsteps.get(idx);
            DpllSolver.Snapshot prev = idx > 0 ? dsteps.get(idx - 1) : null;
            BufferedImage img = new BufferedImage(1100, 780, BufferedImage.TYPE_INT_RGB);
            java.awt.Graphics2D g = img.createGraphics();
            GraphView.TreeLayout curT = GraphView.treeLayout(cur);
            GraphView.TreeLayout prevT = GraphView.treeLayout(prev);
            GraphView.paintTree(g, 1100, 780, cur, prev, 1.0, curT, prevT,
                    0, 0, 1.0, idx + 1, dsteps.size());
            g.dispose();
            File f = new File(outDir, "dpll_step" + idx + ".png");
            ImageIO.write(img, "png", f);
            System.out.println("  " + f);
        }

        System.out.println("frames written to " + outDir);
    }

    static void exportTrace(Trace trace, String name, String outDir, int[] indices) throws Exception {
        for (int idx : indices) {
            idx = Math.max(0, Math.min(trace.steps.size() - 1, idx));
            Trace.Step cur = trace.steps.get(idx);
            Trace.Step prev = idx > 0 ? trace.steps.get(idx - 1) : null;
            BufferedImage img = new BufferedImage(1100, 780, BufferedImage.TYPE_INT_RGB);
            java.awt.Graphics2D g = img.createGraphics();
            GraphView.Layout curL = GraphView.layout(cur);
            GraphView.Layout prevL = GraphView.layout(prev);
            int learnedCount = (int) cur.learned.stream().filter(r -> r[1] == 1).count();
            GraphView.paint(g, 1100, 780, cur, prev, 1.0, curL, prevL, 0, 0, 1.0, learnedCount);
            g.dispose();
            File f = new File(outDir, name + "_step" + idx + ".png");
            ImageIO.write(img, "png", f);
            System.out.println("  " + f);
        }
    }
}
