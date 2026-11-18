package satviz;

import java.awt.*;
import java.awt.geom.*;
import java.util.*;
import java.util.List;

/**
 * Implication-graph renderer: a clean top-down layered diagram — decision
 * level bands from top to bottom, propagated literals hanging below their
 * reasons on curved colored edges, conflict in rose, dashed amber backjump
 * arrow. Paints to any Graphics2D so the live panel and the headless PNG
 * export share identical drawing.
 */
public final class GraphView {

    // ---- palette -------------------------------------------------------
    public static final Color BG        = new Color(0x0a0e1a);
    static final Color GUIDE     = new Color(0x1a2338);
    static final Color NODE_FILL = new Color(0x121a2c);
    static final Color NODE_HI   = new Color(0x26344f);
    static final Color TRUE      = new Color(0x34d399);   // emerald
    static final Color FALSE     = new Color(0x60a5fa);   // blue
    static final Color CONFLICT  = new Color(0xfb7185);   // rose
    static final Color BACKJUMP  = new Color(0xfbbf24);   // amber
    static final Color UIP_RING  = new Color(0xc084fc);   // purple
    static final Color TEXT      = new Color(0xe6edf3);
    static final Color SUBTLE    = new Color(0x77839b);

    static final int NODE_R = 21;
    static final int BAND_H = 96;
    static final int SLOT_W = 68;

    /** Node positions computed for one step. */
    public static final class Layout {
        public final Map<Integer, Point2D.Double> pos = new HashMap<>();
        public final Map<Integer, Integer> levelOf = new HashMap<>();  // var -> decision level
        public final Set<Integer> decisions = new HashSet<>();
        public final Map<Integer, Integer> rowLevel = new LinkedHashMap<>(); // row -> level label
        public double width = 0, height = 0;   // graph bounds for auto-fit
        public int focusVar = 0;
        public int conflictVar = 0;      // var to draw the red halo on
        public int assertedVar = 0;      // backjump target
        public int ghostVar = 0;         // node that just vanished (backjump)
    }

    /**
     * Compute positions as a top-down layered DAG, like the classic
     * implication-graph diagram: decisions and level-0 units on the top
     * row, every propagated literal one row below its reason — row =
     * implication depth, x spread within a row in trail order.
     */
    public static Layout layout(Trace.Step step) {
        Layout L = new Layout();
        if (step == null) return L;
        int n = step.assign.length - 1;
        int[] depth = new int[n + 1];
        Arrays.fill(depth, -1);
        // edges reason -> implied; reasons are always earlier on the trail
        Map<Integer, List<Integer>> preds = new HashMap<>();
        for (Trace.Edge e : step.edges) preds.computeIfAbsent(e.to(), k -> new ArrayList<>()).add(e.from());
        // trail order is a topological order of the implication DAG
        for (int[] r : step.trail) {
            int v = r[0];
            L.levelOf.put(v, r[3]);
            if (r[2] == -1 && r[3] > 0) L.decisions.add(v);
            int d = 0;
            List<Integer> ps = preds.get(v);
            if (ps != null) for (int p : ps) if (depth[p] >= 0) d = Math.max(d, depth[p] + 1);
            depth[v] = d;
        }
        // group by depth row, x spread in trail order
        Map<Integer, List<Integer>> rows = new LinkedHashMap<>();
        for (int[] r : step.trail) rows.computeIfAbsent(depth[r[0]], k -> new ArrayList<>()).add(r[0]);
        List<Integer> rowKeys = new ArrayList<>(rows.keySet());
        Collections.sort(rowKeys);
        for (int row : rowKeys) {
            List<Integer> nodes = rows.get(row);
            int perRow = 12;
            int sub = row * 2;   // sub-row offset reserved for wrapping
            int subRows = (nodes.size() + perRow - 1) / perRow;
            for (int i = 0; i < nodes.size(); i++) {
                int v = nodes.get(i);
                int sr = i / perRow;
                int inRow = i % perRow;
                int inRowCount = Math.min(perRow, nodes.size() - sr * perRow);
                double x = (inRow - (inRowCount - 1) / 2.0) * SLOT_W;
                double y = (sub + sr) * BAND_H;
                L.pos.put(v, new Point2D.Double(x, y));
                if (sr == 0 && !L.rowLevel.containsKey(sub)) L.rowLevel.put(sub, row);
                L.height = Math.max(L.height, y + NODE_R);
            }
            if (subRows > 1) sub += subRows; // keep following rows clear (simple: only demo sizes matter)
        }
        double maxHalf = 0;
        for (List<Integer> nodes : rows.values()) {
            for (int v : nodes) maxHalf = Math.max(maxHalf, Math.abs(L.pos.get(v).x) + NODE_R + 24);
        }
        L.width = maxHalf * 2;

        L.focusVar = step.focusVar;
        if (step.kind == Trace.Kind.CONFLICT && step.trail.size() > 0) {
            int last = step.trail.get(step.trail.size() - 1)[0];
            L.conflictVar = last;
        }
        if (step.kind == Trace.Kind.ASSERT) L.assertedVar = step.focusVar;
        if (step.kind == Trace.Kind.BACKJUMP && step.trail.size() > 0) {
            L.ghostVar = step.trail.get(step.trail.size() - 1)[0];
        }
        return L;
    }

    /** Deterministic pleasant hue per clause id. */
    static Color clauseColor(int id) {
        float h = (id * 0.6180339887f) % 1f;
        return Color.getHSBColor(h, 0.62f, 0.78f);
    }

    static double ease(double t) {          // ease-out cubic
        return t < 0 ? 0 : t > 1 ? 1 : 1 - Math.pow(1 - t, 3);
    }

    static double easeBack(double t) {      // ease-out back: slight overshoot for pop-in
        if (t <= 0) return 0;
        if (t >= 1) return 1;
        double c1 = 1.70158, c3 = c1 + 1, x = t - 1;
        return 1 + c3 * x * x * x + c1 * x * x;
    }

    static Point2D.Double lerp(Point2D.Double a, Point2D.Double b, double t) {
        if (a == null) return b;
        if (b == null) return a;
        return new Point2D.Double(a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t);
    }

    /**
     * Paint the graph. animT in [0,1] animates the newest elements;
     * prevLayout (nullable) enables position gliding and backjump ghosts.
     */
    public static void paint(Graphics2D g, int w, int h,
                             Trace.Step step, Trace.Step prevStep,
                             double animT, Layout L, Layout prevL,
                             double panX, double panY, double zoom,
                             int learnedCount) {
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
        g.setRenderingHint(RenderingHints.KEY_STROKE_CONTROL, RenderingHints.VALUE_STROKE_PURE);
        g.setColor(BG);
        g.fillRect(0, 0, w, h);

        if (step == null || step.trail.isEmpty() && step.kind != Trace.Kind.INIT) return;

        Font nodeFont = new Font(Font.DIALOG, Font.BOLD, 13);
        Font tagFont = new Font(Font.DIALOG, Font.PLAIN, 10);

        // auto-fit: scale the graph to fill the panel (user zoom multiplies)
        double fit = 1.0;
        if (L.width > 0 && L.height > 0) {
            double availW = w - 120, availH = h - 140;
            fit = Math.min(availW / L.width, availH / L.height);
            fit = Math.max(0.35, Math.min(2.2, fit));
        }
        double useZoom = fit * zoom;

        AffineTransform base = g.getTransform();
        g.translate(w / 2.0 + panX, 64 + panY);
        g.scale(useZoom, useZoom);

        double t = ease(animT);

        // ---- effective positions: glide from previous layout to this one --
        Map<Integer, Point2D.Double> eff = new HashMap<>();
        for (Map.Entry<Integer, Point2D.Double> e : L.pos.entrySet()) {
            Point2D.Double pr = prevL != null ? prevL.pos.get(e.getKey()) : null;
            eff.put(e.getKey(), pr != null && t < 1 ? lerp(pr, e.getValue(), t) : e.getValue());
        }

        // ---- level guide lines (the downward structure) --------------------
        for (Map.Entry<Integer, Integer> e : L.rowLevel.entrySet()) {
            double y = e.getKey() * BAND_H - NODE_R - 14;
            g.setColor(GUIDE);
            g.setStroke(new BasicStroke(1f, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER,
                    10f, new float[]{2f, 6f}, 0f));
            g.draw(new Line2D.Double(-2600, y, 2600, y));
        }

        // ---- edges (implication graph) --------------------------------
        // group edges by clause id so a reason clause draws as one bundle
        Map<Integer, List<int[]>> byClause = new LinkedHashMap<>();
        for (Trace.Edge e : step.edges) {
            byClause.computeIfAbsent(e.clauseId(), k -> new ArrayList<>())
                    .add(new int[]{e.from(), e.to()});
        }
        for (Map.Entry<Integer, List<int[]>> e : byClause.entrySet()) {
            int cid = e.getKey();
            Color col = clauseColor(cid);
            for (int[] ee : e.getValue()) {
                Point2D.Double a = eff.get(ee[0]);
                Point2D.Double b = eff.get(ee[1]);
                if (a == null || b == null) continue;
                drawEdge(g, a, b, col, cid, Math.min(1, t * 1.6), Math.min(1, animT * 2));
            }
        }

        // ---- backjump arrow (dashed, from removed decision to assert) --
        if ((step.kind == Trace.Kind.BACKJUMP || step.kind == Trace.Kind.ASSERT)
                && prevL != null && prevL.conflictVar != 0) {
            Point2D.Double from = prevL.pos.get(prevL.conflictVar);
            Point2D.Double to;
            if (step.kind == Trace.Kind.ASSERT) {
                to = eff.get(step.focusVar);
            } else {
                to = eff.get(step.focusVar != 0 ? step.focusVar : prevL.conflictVar);
            }
            if (from != null && to != null) {
                drawBackjump(g, from, to, t);
            }
        }

        // ---- nodes ------------------------------------------------------
        for (int[] r : step.trail) {
            int v = r[0];
            boolean val = r[1] == 1;
            int reason = r[2];
            int lvl = r[3];
            Point2D.Double p = eff.get(v);
            if (p == null) continue;

            boolean isNew = L.focusVar == v
                    && (step.kind == Trace.Kind.DECIDE
                     || step.kind == Trace.Kind.ASSERT
                     || step.kind == Trace.Kind.PROPAGATE);
            double scale = isNew ? 0.35 + 0.65 * easeBack(animT) : 1.0;
            if (scale <= 0.01) continue;

            boolean isConflict = (v == L.conflictVar && step.kind == Trace.Kind.CONFLICT);
            boolean isUIP = (step.kind == Trace.Kind.LEARN && v == step.focusVar);

            drawNode(g, p.x, p.y, v, val, L.decisions.contains(v), reason, lvl,
                     scale, isConflict, isUIP, isConflict ? t : -1,
                     nodeFont, tagFont);
        }

        // ghost of the deepest removed node on a backjump
        if (L.ghostVar != 0 && prevL != null && animT < 1) {
            Point2D.Double gp = prevL.pos.get(L.ghostVar);
            if (gp != null) {
                Composite old = g.getComposite();
                g.setComposite(AlphaComposite.SrcOver.derive((float) (1 - t) * 0.55f));
                drawNode(g, gp.x, gp.y, L.ghostVar, false, false, -2, -1,
                         1.0 + 0.35 * t, false, false, -1, nodeFont, tagFont);
                g.setComposite(old);
            }
        }

        g.setTransform(base);

        // ---- row labels in screen space -----------------------------------
        g.setFont(tagFont);
        for (Map.Entry<Integer, Integer> e : L.rowLevel.entrySet()) {
            int row = e.getKey();
            if (e.getValue() == 0) continue;   // decisions are tagged on the nodes
            int ly = (int) (64 + panY + (row * BAND_H - NODE_R - 20) * useZoom);
            if (ly < 20 || ly > h - 30) continue;
            g.setColor(SUBTLE);
            g.drawString("propagation layer " + e.getValue(), 16, ly);
        }

        // ---- kind banner ---------------------------------------------------
        String banner = switch (step.kind) {
            case DECIDE -> "DECIDE";
            case PROPAGATE -> "PROPAGATE";
            case CONFLICT -> "CONFLICT";
            case RESOLVE -> "RESOLVE";
            case LEARN -> "LEARN";
            case BACKJUMP -> "BACKJUMP";
            case ASSERT -> "ASSERT";
            case RESTART -> "RESTART";
            case REDUCE -> "REDUCE DB";
            case SAT -> "SAT";
            case UNSAT -> "UNSAT";
            case INIT -> "FORMULA";
        };
        Color bannerCol = switch (step.kind) {
            case CONFLICT -> CONFLICT;
            case LEARN -> UIP_RING;
            case SAT -> TRUE;
            case UNSAT -> CONFLICT;
            case DECIDE -> BACKJUMP;
            case ASSERT -> BACKJUMP;
            default -> SUBTLE;
        };
        g.setFont(new Font(Font.DIALOG, Font.BOLD, 15));
        FontMetrics fm = g.getFontMetrics();
        int bx = 16, by = 30;
        g.setColor(new Color(0, 0, 0, 0.4f));
        g.fillRoundRect(bx - 8, by - 18, fm.stringWidth(banner) + 16, 26, 8, 8);
        g.setColor(bannerCol);
        g.drawString(banner, bx, by);

        // footer
        g.setFont(tagFont);
        g.setColor(SUBTLE);
        g.drawString("learned clauses: " + learnedCount + "    wheel = zoom, drag = pan", 16, h - 12);
    }

    /** Cubic bezier pointing downward from a to b, with glow + arrowhead. */
    static void drawEdge(Graphics2D g, Point2D.Double a, Point2D.Double b,
                         Color col, int cid, double grow, double alphaT) {
        double x1 = a.x, y1 = a.y + NODE_R;
        double x2 = b.x, y2 = b.y - NODE_R - 2;
        double drop = Math.max(26, (y2 - y1) * 0.45);
        double cy1 = y1 + drop, cy2 = y2 - drop;
        int alpha = (int) (200 * Math.min(1, alphaT));
        Color core = new Color(col.getRed(), col.getGreen(), col.getBlue(), alpha);
        Color glow = new Color(col.getRed(), col.getGreen(), col.getBlue(), alpha / 4);

        Path2D path = partialBezier(x1, y1, x1, cy1, x2, cy2, x2, y2, Math.min(1, grow));

        // soft glow underneath, crisp core on top
        g.setStroke(new BasicStroke(5.5f, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND));
        g.setColor(glow);
        g.draw(path);
        g.setStroke(new BasicStroke(2.1f, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND));
        g.setColor(core);
        g.draw(path);

        // arrowhead oriented along the curve tangent
        double gt = Math.min(1, grow);
        double hx = bez(x1, x1, x2, x2, gt);
        double hy = bez(y1, cy1, cy2, y2, gt);
        double ex = bez(x1, x1, x2, x2, Math.max(0, gt - 0.02));
        double ey = bez(y1, cy1, cy2, y2, Math.max(0, gt - 0.02));
        arrowHead(g, hx, hy, hx - ex, hy - ey, core);

        // clause label chip at midpoint
        if (grow >= 1 && cid >= 0) {
            double mx = bez(x1, x1, x2, x2, 0.5);
            double my = bez(y1, cy1, cy2, y2, 0.5);
            String lbl = "c" + cid;
            Font f = new Font(Font.DIALOG, Font.BOLD, 9);
            g.setFont(f);
            FontMetrics fm = g.getFontMetrics();
            double lw = fm.stringWidth(lbl);
            g.setColor(new Color(0x0a0e1a, true));
            g.fillRoundRect((int) (mx - lw / 2 - 3), (int) (my - 8), (int) lw + 6, 13, 6, 6);
            g.setColor(col);
            g.drawString(lbl, (float) (mx - lw / 2), (float) (my + 2.5));
        }
    }

    /** Flattened cubic bezier, drawn only up to fraction grow. */
    static Path2D partialBezier(double x1, double y1, double cx1, double cy1,
                                double cx2, double cy2, double x2, double y2, double grow) {
        Path2D path = new Path2D.Double();
        int steps = 48;
        int n = Math.max(1, (int) (steps * grow));
        for (int i = 0; i <= n; i++) {
            double tt = i / (double) steps;
            double x = bez(x1, cx1, cx2, x2, tt);
            double y = bez(y1, cy1, cy2, y2, tt);
            if (i == 0) path.moveTo(x, y); else path.lineTo(x, y);
        }
        return path;
    }

    /** Filled arrowhead at (x,y) pointing along (dx,dy). */
    static void arrowHead(Graphics2D g, double x, double y, double dx, double dy, Color col) {
        double ang = Math.atan2(dy, dx);
        AffineTransform old = g.getTransform();
        g.translate(x, y);
        g.rotate(ang);
        g.setColor(col);
        Path2D p = new Path2D.Double();
        p.moveTo(0, 0);
        p.lineTo(-10, -4.6);
        p.lineTo(-7, 0);
        p.lineTo(-10, 4.6);
        p.closePath();
        g.fill(p);
        g.setTransform(old);
    }

    static double bez(double a, double c1, double c2, double b, double t) {
        double u = 1 - t;
        return u * u * u * a + 3 * u * u * t * c1 + 3 * u * t * t * c2 + t * t * t * b;
    }

    static void drawBackjump(Graphics2D g, Point2D.Double from, Point2D.Double to, double t) {
        double x1 = from.x, y1 = from.y - NODE_R - 4;
        double x2 = to.x, y2 = to.y - NODE_R - 4;
        double mx = (x1 + x2) / 2, my = Math.min(y1, y2) - 52;
        Color col = BACKJUMP;
        int alpha = (int) (230 * Math.min(1, t * 1.5));
        col = new Color(col.getRed(), col.getGreen(), col.getBlue(), alpha);

        // glow + dashed core
        Path2D path = new Path2D.Double();
        int steps = 48;
        int n = Math.max(1, (int) (steps * Math.min(1, t)));
        for (int i = 0; i <= n; i++) {
            double tt = i / (double) steps, u = 1 - tt;
            double x = u * u * x1 + 2 * u * tt * mx + tt * tt * x2;
            double y = u * u * y1 + 2 * u * tt * my + tt * tt * y2;
            if (i == 0) path.moveTo(x, y); else path.lineTo(x, y);
        }
        g.setStroke(new BasicStroke(6.5f, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND));
        g.setColor(new Color(col.getRed(), col.getGreen(), col.getBlue(), alpha / 4));
        g.draw(path);
        g.setStroke(new BasicStroke(2.4f, BasicStroke.CAP_BUTT, BasicStroke.JOIN_MITER,
                10f, new float[]{8f, 6f}, 0f));
        g.setColor(col);
        g.draw(path);

        // arrowhead along tangent at the tip
        double et = Math.min(1, t);
        double u = 1 - et;
        double hx = u * u * x1 + 2 * u * et * mx + et * et * x2;
        double hy = u * u * y1 + 2 * u * et * my + et * et * y2;
        double et2 = Math.max(0, et - 0.02), u2 = 1 - et2;
        double px = u2 * u2 * x1 + 2 * u2 * et2 * mx + et2 * et2 * x2;
        double py = u2 * u2 * y1 + 2 * u2 * et2 * my + et2 * et2 * y2;
        arrowHead(g, hx, hy, hx - px, hy - py, col);

        g.setFont(new Font(Font.DIALOG, Font.BOLD, 10));
        g.setColor(col);
        g.drawString("backjump", (float) hx + 8, (float) hy - 6);
    }

    static void drawNode(Graphics2D g, double x, double y, int v, boolean val,
                         boolean decision, int reason, int lvl, double scale,
                         boolean conflict, boolean uip, double pulseT,
                         Font nodeFont, Font tagFont) {        double r = NODE_R * scale;
        Color ring = conflict ? CONFLICT : val ? TRUE : FALSE;

        // conflict pulse halo
        if (conflict && pulseT >= 0) {
            double pr = r + 6 + 12 * pulseT;
            g.setColor(new Color(CONFLICT.getRed(), CONFLICT.getGreen(), CONFLICT.getBlue(),
                    (int) (150 * (1 - pulseT))));
            g.setStroke(new BasicStroke(2.5f));
            g.draw(new Ellipse2D.Double(x - pr, y - pr, 2 * pr, 2 * pr));
        }
        // UIP ring
        if (uip) {
            g.setColor(UIP_RING);
            g.setStroke(new BasicStroke(2.5f));
            double ur = r + 5;
            g.draw(new Ellipse2D.Double(x - ur, y - ur, 2 * ur, 2 * ur));
        }
        // body: subtle radial gradient
        Point2D.Double hi = new Point2D.Double(x - r * 0.35, y - r * 0.4);
        g.setPaint(new RadialGradientPaint(hi, (float) (r * 1.5),
                new float[]{0f, 1f}, new Color[]{NODE_HI, NODE_FILL}));
        g.fill(new Ellipse2D.Double(x - r, y - r, 2 * r, 2 * r));
        g.setColor(conflict ? CONFLICT : decision ? BACKJUMP : ring);
        g.setStroke(new BasicStroke(conflict || decision ? 2.4f : 1.8f));
        g.draw(new Ellipse2D.Double(x - r, y - r, 2 * r, 2 * r));
        // inner value dot
        g.setColor(ring);
        g.fill(new Ellipse2D.Double(x - 2.5, y + r - 8.5, 5, 5));

        // label
        g.setFont(nodeFont);
        g.setColor(TEXT);
        String s = "x" + v;
        FontMetrics fm = g.getFontMetrics();
        g.drawString(s, (float) (x - fm.stringWidth(s) / 2.0), (float) (y + 4.5 * scale));

        // tag under node
        g.setFont(tagFont);
        Color tagCol = decision ? BACKJUMP : conflict ? CONFLICT : SUBTLE;
        g.setColor(tagCol);
        String tag = decision ? "decision" : conflict ? "conflict" : "L" + lvl;
        g.drawString(tag, (float) (x - g.getFontMetrics().stringWidth(tag) / 2.0), (float) (y + r + 14));
    }

// =====================================================================
// DPLL search-tree rendering (second visualization mode)
// =====================================================================

public static final class TreeLayout {
    public final java.util.Map<Integer, Point2D.Double> pos = new java.util.HashMap<>();
    public double width = 0, height = 0;
}

/**
 * Tidy layout for the DPLL search tree: leaves left-to-right in creation
 * order, parents centered over children, y by depth.
 */
public static TreeLayout treeLayout(DpllSolver.Snapshot snap) {
    TreeLayout T = new TreeLayout();
    if (snap == null || snap.nodes.isEmpty()) return T;
    java.util.Map<Integer, java.util.List<Integer>> kids = new java.util.HashMap<>();
    java.util.Set<Integer> hasParent = new java.util.HashSet<>();
    for (DpllSolver.TNode n : snap.nodes) {
        if (n.parent != 0) {
            kids.computeIfAbsent(n.parent, k -> new java.util.ArrayList<>()).add(n.id);
            hasParent.add(n.id);
        }
    }
    // leaves in creation order
    double x = 0;
    for (DpllSolver.TNode n : snap.nodes) {
        if (!kids.containsKey(n.id)) {
            T.pos.put(n.id, new Point2D.Double(x * SLOT_W, n.depth * BAND_H));
            x++;
        }
    }
    // internal nodes: post-order mean of children, y from depth
    java.util.Map<Integer, Point2D.Double> fin = new java.util.HashMap<>();
    for (DpllSolver.TNode n : snap.nodes) {
        if (!kids.containsKey(n.id)) fin.put(n.id, T.pos.get(n.id));
    }
    for (DpllSolver.TNode n : snap.nodes) {
        if (kids.containsKey(n.id)) fin.put(n.id, centerOver(kids.get(n.id), fin, n.depth));
    }
    T.pos.putAll(fin);
    // enforce a minimum horizontal gap between same-depth nodes (left→right)
    java.util.List<DpllSolver.TNode> ordered = new java.util.ArrayList<>(snap.nodes);
    double minGap = 2 * NODE_R + 16;
    for (int pass = 0; pass < 2; pass++) {
        java.util.Map<Integer, java.util.List<Integer>> byDepth = new java.util.LinkedHashMap<>();
        for (DpllSolver.TNode n : ordered) {
            byDepth.computeIfAbsent(n.depth, k -> new java.util.ArrayList<>()).add(n.id);
        }
        for (java.util.List<Integer> row : byDepth.values()) {
            for (int i = 1; i < row.size(); i++) {
                Point2D.Double prev = T.pos.get(row.get(i - 1));
                Point2D.Double cur = T.pos.get(row.get(i));
                if (prev != null && cur != null && cur.x - prev.x < minGap) {
                    cur.setLocation(prev.x + minGap, cur.y);
                }
            }
        }
    }
    double minX = 0;
    for (Point2D.Double p : T.pos.values()) {
        minX = Math.min(minX, p.x - NODE_R - 24);
        T.width = Math.max(T.width, p.x + NODE_R + 24);
        T.height = Math.max(T.height, p.y + NODE_R + 16);
    }
    // shift so the leftmost node clears the origin
    if (minX < 0) {
        for (Map.Entry<Integer, Point2D.Double> e : T.pos.entrySet())
            e.setValue(new Point2D.Double(e.getValue().x - minX, e.getValue().y));
        T.width -= minX;
    }
    T.width = Math.max(T.width, SLOT_W);
    return T;
}

private static Point2D.Double centerOver(java.util.List<Integer> childIds,
                                         java.util.Map<Integer, Point2D.Double> fin, int depth) {
    double sx = 0; int cnt = 0;
    for (int c : childIds) {
        Point2D.Double p = fin.get(c);
        if (p != null) { sx += p.x; cnt++; }
    }
    return new Point2D.Double(cnt > 0 ? sx / cnt : 0, depth * BAND_H);
}

/**
 * Paint the DPLL search tree. animT animates the newest node/edge;
 * prevSnap enables node gliding.
 */
public static void paintTree(Graphics2D g, int w, int h,
                      DpllSolver.Snapshot snap, DpllSolver.Snapshot prevSnap,
                      double animT, TreeLayout T, TreeLayout prevT,
                      double panX, double panY, double zoom,
                      int stepNum, int totalSteps) {
    g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
    g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING, RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
    g.setRenderingHint(RenderingHints.KEY_STROKE_CONTROL, RenderingHints.VALUE_STROKE_PURE);
    g.setColor(BG);
    g.fillRect(0, 0, w, h);
    if (snap == null || snap.nodes.isEmpty()) return;

    Font nodeFont = new Font(Font.DIALOG, Font.BOLD, 12);
    Font tagFont = new Font(Font.DIALOG, Font.PLAIN, 10);

    double fit = 1.0;
    if (T.width > 0 && T.height > 0) {
        double availW = w - 120, availH = h - 140;
        fit = Math.min(availW / T.width, availH / T.height);
        fit = Math.max(0.3, Math.min(2.0, fit));
    }
    double useZoom = fit * zoom;

    AffineTransform base = g.getTransform();
    // center the content (x spans 0..T.width), not the origin
    g.translate(w / 2.0 - (T.width / 2.0) * useZoom + panX, 70 + panY);
    g.scale(useZoom, useZoom);

    double t = ease(animT);
    double growX = snap.focusNode != 0 && T.pos.containsKey(snap.focusNode)
            ? T.pos.get(snap.focusNode).x : 0;

    // ---- edges ----------------------------------------------------------
    java.util.Map<Integer, DpllSolver.TNode> byId = new java.util.HashMap<>();
    for (DpllSolver.TNode n : snap.nodes) byId.put(n.id, n);
    for (DpllSolver.TNode n : snap.nodes) {
        if (n.parent == 0) continue;
        Point2D.Double a = T.pos.get(n.parent);
        Point2D.Double b = T.pos.get(n.id);
        if (a == null || b == null) continue;
        boolean isNew = n.id == snap.focusNode;
        double gr = isNew ? t : 1;
        // partial grow: draw from parent toward child
        double gx = a.x + (b.x - a.x) * gr;
        double gy = a.y + (b.y - a.y) * gr;
        Color col = edgeColor(n, byId);
        // glow + core line
        g.setStroke(new BasicStroke(5f, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND));
        g.setColor(new Color(col.getRed(), col.getGreen(), col.getBlue(), 45));
        g.draw(new Line2D.Double(a.x, a.y, gx, gy));
        g.setStroke(new BasicStroke(2f, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND));
        g.setColor(col);
        g.draw(new Line2D.Double(a.x, a.y, gx, gy));
        if (gr >= 1) {
            arrowHead(g, b.x, b.y - NODE_R, b.x - a.x, b.y - a.y, col);
        }
    }

    // ---- nodes -----------------------------------------------------------
    for (DpllSolver.TNode n : snap.nodes) {
        Point2D.Double p = T.pos.get(n.id);
        if (p == null) continue;
        boolean isNew = n.id == snap.focusNode;
        double scale = isNew ? 0.35 + 0.65 * easeBack(animT) : 1.0;
        boolean onPath = snap.pathNodes.contains(n.id);
        Color ring = nodeColor(n, onPath);
        // body: diamond for conflict nodes, circle otherwise
        java.awt.Shape body;
        if (n.kind == 'C') {
            double r = NODE_R * scale * 1.12;
            java.awt.geom.Path2D.Double d = new java.awt.geom.Path2D.Double();
            d.moveTo(p.x, p.y - r);
            d.lineTo(p.x + r, p.y);
            d.lineTo(p.x, p.y + r);
            d.lineTo(p.x - r, p.y);
            d.closePath();
            body = d;
        } else {
            double r = NODE_R * scale;
            body = new Ellipse2D.Double(p.x - r, p.y - r, 2 * r, 2 * r);
        }
        Point2D.Double hi = new Point2D.Double(p.x - NODE_R * 0.35, p.y - NODE_R * 0.4);
        g.setPaint(new RadialGradientPaint(hi, (float) (NODE_R * 1.5),
                new float[]{0f, 1f},
                new Color[]{n.kind == 'C' ? new Color(0x3a1b26) : NODE_HI, NODE_FILL}));
        g.fill(body);
        g.setColor(ring);
        g.setStroke(new BasicStroke(onPath ? 2.4f : 1.6f));
        g.draw(body);
        // label: decision/propagation literal, conflict glyph
        g.setFont(nodeFont);
        g.setColor(TEXT);
        String s = n.kind == 'C' ? "✗" : litLabel(n.lit);
        if (n.kind == 'C') g.setColor(CONFLICT);
        FontMetrics fm = g.getFontMetrics();
        g.drawString(s, (float) (p.x - fm.stringWidth(s) / 2.0), (float) (p.y + 4 * scale));
        // status tag
        if (n.status != DpllSolver.OPEN || n.kind == 'C') {
            g.setFont(tagFont);
            String tag = n.kind == 'C' ? "conflict"
                    : n.status == DpllSolver.SAT ? "SAT"
                    : n.status == DpllSolver.UNSAT ? "UNSAT" : "cut";
            Color tc = n.kind == 'C' ? CONFLICT
                    : n.status == DpllSolver.SAT ? TRUE
                    : n.status == DpllSolver.UNSAT ? CONFLICT : SUBTLE;
            g.setColor(tc);
            g.drawString(tag, (float) (p.x - g.getFontMetrics().stringWidth(tag) / 2.0),
                    (float) (p.y + NODE_R + 14));
        }
    }

    // ---- path assignment strip (top, in graph coords) ---------------------
    g.setFont(tagFont);
    double ax = -T.width / 2 + 10;
    double ay = -NODE_R - 26;
    StringBuilder sb = new StringBuilder();
    for (int[] pa : snap.pathAssigns) {
        if (sb.length() > 0) sb.append("  ");
        sb.append("x").append(pa[0]).append("=").append(pa[1] == 1 ? "T" : "F");
    }
    String asg = sb.length() == 0 ? "(nothing assigned yet)" : sb.toString();
    g.setColor(SUBTLE);
    g.drawString(asg, (float) ax, (float) ay);

    g.setTransform(base);

    // ---- banner ----------------------------------------------------------
    String banner = switch (snap.kind) {
        case DECIDE -> "BRANCH";
        case PROPAGATE -> "UNIT/PURE";
        case CONFLICT -> "CONFLICT";
        case BACKJUMP -> "BACKTRACK";
        case SAT -> "SAT";
        case UNSAT -> "UNSAT";
        case INIT -> "FORMULA";
        default -> snap.kind.label.toUpperCase();
    };
    Color bannerCol = switch (snap.kind) {
        case CONFLICT -> CONFLICT;
        case SAT -> TRUE;
        case UNSAT -> CONFLICT;
        case DECIDE -> BACKJUMP;
        default -> SUBTLE;
    };
    g.setFont(new Font(Font.DIALOG, Font.BOLD, 15));
    FontMetrics fm = g.getFontMetrics();
    int bx = 16, by = 30;
    g.setColor(new Color(0, 0, 0, 0.4f));
    g.fillRoundRect(bx - 8, by - 18, fm.stringWidth(banner) + 16, 26, 8, 8);
    g.setColor(bannerCol);
    g.drawString(banner, bx, by);

    g.setFont(tagFont);
    g.setColor(SUBTLE);
    g.drawString("step " + stepNum + "/" + totalSteps + "    wheel = zoom, drag = pan", 16, h - 12);
}

private static Color edgeColor(DpllSolver.TNode n, java.util.Map<Integer, DpllSolver.TNode> byId) {
    if (n.kind == 'C') return CONFLICT;
    if (n.status == DpllSolver.UNSAT) return new Color(CONFLICT.getRed(), CONFLICT.getGreen(), CONFLICT.getBlue(), 140);
    if (n.status == DpllSolver.SAT) return new Color(TRUE.getRed(), TRUE.getGreen(), TRUE.getBlue(), 170);
    if (n.kind == 'P') return new Color(0x3b82f6);      // propagation edge: blue
    return new Color(0x5b6b8c);
}

private static Color nodeColor(DpllSolver.TNode n, boolean onPath) {
    if (n.kind == 'C') return CONFLICT;
    if (n.status == DpllSolver.SAT) return TRUE;
    if (n.status == DpllSolver.UNSAT) return CONFLICT;
    if (onPath) return BACKJUMP;
    if (n.kind == 'P') return new Color(0x60a5fa);      // propagation node: light blue
    return new Color(0x8294b5);
}

private static String litLabel(int lit) {
    return (lit < 0 ? "¬" : "") + "x" + Math.abs(lit);
}

}