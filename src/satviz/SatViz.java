package satviz;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.File;
import java.nio.file.*;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.Timer;

/**
 * SATviz — animated CDCL visualizer. Shows the implication graph growing
 * step by step: decisions, propagations, conflicts, resolution, learned
 * clauses, backjumps — like the classic implication-graph diagram, alive.
 *
 * CLI:
 *   java -jar satviz.jar                 — GUI
 *   java -jar satviz.jar --test          — self-tests
 *   java -jar satviz.jar --render DIR    — headless PNG frames of a demo trace
 *   java -jar satviz.jar --solve F.cnf   — headless solve (exit 10/20 per DIMACS)
 */
public final class SatViz extends JFrame {

    private Trace trace;                       // CDCL trace
    private List<DpllSolver.Snapshot> dpllSteps; // DPLL snapshots
    private boolean dpllMode = false;
    private int stepIdx = 0;
    private GraphView.Layout prevLayout, curLayout;
    private GraphView.TreeLayout prevTree, curTree;
    private long stepTime = 0;
    private boolean playing = false;
    private int playDelayMs = 700;

    private final GraphPanel graphPanel = new GraphPanel();
    private final JTextArea infoArea = new JTextArea();
    private final JTextArea learnedArea = new JTextArea();
    private final JTextArea trailArea = new JTextArea();
    private JScrollPane infoScroll, learnedScroll, trailScroll;
    private final JSlider scrubber = new JSlider(0, 0, 0);
    private final JLabel stats = new JLabel(" ");
    private final Timer animTimer = new Timer(16, e -> onAnimTick());
    private final Timer playTimer = new Timer(playDelayMs, e -> next());
    private final JButton playBtn = new JButton("▶ Play");

    public SatViz() {
        super("SATviz — CDCL & DPLL, animated");
        setDefaultCloseOperation(EXIT_ON_CLOSE);
        setSize(1280, 800);
        setLocationRelativeTo(null);

        // ---- top toolbar
        JComboBox<String> algo = new JComboBox<>(new String[]{
                "Algorithm: CDCL (implication graph)",
                "Algorithm: DPLL (search tree)",
        });
        algo.addActionListener(e -> {
            dpllMode = algo.getSelectedIndex() == 1;
            recolorBorders(trailScroll, dpllMode ? "current assignment" : "assignment trail");
            solve();
        });
        JComboBox<String> presets = new JComboBox<>(new String[]{
                "Preset: implication chain → conflict",
                "Preset: diamond (2-var UNSAT)",
                "Preset: pigeonhole PHP(3,2)",
                "Preset: random 3-SAT (8 vars, 3 conflicts)",
        });
        presets.addActionListener(e -> {
            loadPreset(presets.getSelectedIndex());
            presets.setSelectedIndex(-1);
        });
        JButton loadBtn = new JButton("Open DIMACS…");
        loadBtn.addActionListener(e -> loadDimacs());
        JSlider speed = new JSlider(100, 2000, playDelayMs);
        speed.addChangeListener(e -> playDelayMs = 2100 - speed.getValue());
        JButton solveBtn = new JButton("Solve");
        solveBtn.addActionListener(e -> solve());

        JToolBar bar = new JToolBar();
        bar.setFloatable(false);
        bar.add(algo);
        bar.add(presets);
        bar.add(loadBtn);
        bar.add(solveBtn);
        bar.add(new JLabel("  speed"));
        bar.add(speed);

        // ---- right side panels
        infoArea.setEditable(false); infoArea.setLineWrap(true); infoArea.setWrapStyleWord(true);
        learnedArea.setEditable(false); learnedArea.setLineWrap(true); learnedArea.setWrapStyleWord(true);
        trailArea.setEditable(false);
        styleArea(infoArea); styleArea(learnedArea); styleArea(trailArea);
        infoScroll = new JScrollPane(infoArea);
        learnedScroll = new JScrollPane(learnedArea);
        trailScroll = new JScrollPane(trailArea);
        infoScroll.setBorder(BorderFactory.createTitledBorder("step"));
        learnedScroll.setBorder(BorderFactory.createTitledBorder("learned clauses"));
        trailScroll.setBorder(BorderFactory.createTitledBorder("assignment trail"));
        JSplitPane rightSplit = new JSplitPane(JSplitPane.VERTICAL_SPLIT, infoScroll, learnedScroll);
        rightSplit.setResizeWeight(0.5);
        JSplitPane rightSplit2 = new JSplitPane(JSplitPane.VERTICAL_SPLIT, rightSplit, trailScroll);
        rightSplit2.setResizeWeight(0.55);

        JSplitPane mainSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, graphPanel, rightSplit2);
        mainSplit.setResizeWeight(0.72);

        // ---- bottom controls
        JButton first = new JButton("⏮"), back = new JButton("◀"),
                fwd = new JButton("▶|"), last = new JButton("⏭");
        first.addActionListener(e -> { setStep(0); });
        back.addActionListener(e -> setStep(stepIdx - 1));
        fwd.addActionListener(e -> next());
        last.addActionListener(e -> setStep(trace == null ? 0 : trace.steps.size() - 1));
        playBtn.addActionListener(e -> togglePlay());
        scrubber.addChangeListener(e -> {
            if (scrubber.getValueIsAdjusting() && !playing) setStep(scrubber.getValue());
        });

        JPanel controls = new JPanel(new BorderLayout());
        JPanel btns = new JPanel();
        for (JButton b : new JButton[]{first, back, playBtn, fwd, last}) btns.add(b);
        controls.add(btns, BorderLayout.WEST);
        controls.add(scrubber, BorderLayout.CENTER);
        controls.add(stats, BorderLayout.EAST);

        add(bar, BorderLayout.NORTH);
        add(mainSplit, BorderLayout.CENTER);
        add(controls, BorderLayout.SOUTH);

        // keyboard: arrows step, space plays
       getRootPane().registerKeyboardAction(e -> setStep(stepIdx - 1),
                KeyStroke.getKeyStroke(KeyEvent.VK_LEFT, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
        getRootPane().registerKeyboardAction(e -> next(),
                KeyStroke.getKeyStroke(KeyEvent.VK_RIGHT, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
        getRootPane().registerKeyboardAction(e -> togglePlay(),
                KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
        getRootPane().registerKeyboardAction(e -> setStep(0),
                KeyStroke.getKeyStroke(KeyEvent.VK_R, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);

        loadPreset(0);
        styleDark();
    }

    private void styleArea(JTextArea a) {
        a.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        a.setBackground(new Color(0x161b22));
        a.setForeground(new Color(0xc9d1d9));
        a.setCaretPosition(0);
    }

    /** Dark theme for the whole chrome: panels, buttons, sliders, combo boxes. */
    private void styleDark() {
        Color bg = new Color(0x0a0e1a);
        Color panel = new Color(0x111827);
        Color fg = new Color(0xe6edf3);
        Color accent = new Color(0xfbbf24);

        UIManager.put("ToolBar.background", panel);
        UIManager.put("ToolBar.foreground", fg);
        UIManager.put("Panel.background", panel);
        UIManager.put("Label.foreground", fg);
        UIManager.put("Button.background", new Color(0x1f2937));
        UIManager.put("Button.foreground", fg);
        UIManager.put("Button.border", BorderFactory.createCompoundBorder(
                BorderFactory.createLineBorder(new Color(0x374151), 1),
                BorderFactory.createEmptyBorder(4, 12, 4, 12)));
        UIManager.put("ComboBox.background", new Color(0x1f2937));
        UIManager.put("ComboBox.foreground", fg);
        UIManager.put("ComboBox.selectionBackground", accent);
        UIManager.put("ComboBox.selectionForeground", new Color(0x0a0e1a));
        UIManager.put("Slider.background", panel);
        UIManager.put("Slider.foreground", accent);
        UIManager.put("ScrollPane.background", bg);
        UIManager.put("Viewport.background", bg);
        UIManager.put("SplitPane.background", bg);
        UIManager.put("SplitPaneDivider.background", panel);
        UIManager.put("TitledBorder.titleColor", new Color(0x9ca3af));
        UIManager.put("OptionPane.background", panel);
        UIManager.put("OptionPane.messageForeground", fg);

        // repaint this frame with the new look
        SwingUtilities.updateComponentTreeUI(this);

        // titled borders need explicit colors on this LAF
        recolorBorders(infoScroll, "step");
        recolorBorders(learnedScroll, "learned clauses");
        recolorBorders(trailScroll, (dpllMode ? "current assignment" : "assignment trail"));
    }

    private void recolorBorders(JScrollPane sp, String title) {
        sp.setBorder(BorderFactory.createTitledBorder(
                BorderFactory.createLineBorder(new Color(0x374151)),
                title,
                javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION,
                javax.swing.border.TitledBorder.DEFAULT_POSITION,
                new Font(Font.DIALOG, Font.BOLD, 11),
                new Color(0x9ca3af)));
    }

    // ------------------------------------------------------------------
    void solve() {
        if (pendingClauses == null) return;
        if (dpllMode) {
            DpllSolver s = new DpllSolver(pendingVars);
            for (int[] c : pendingClauses) s.addClause(c.clone());
            dpllSteps = s.solve();
        } else {
            Solver s = new Solver(pendingVars);
            for (int[] c : pendingClauses) if (!s.addClause(c.clone())) { /* trivial UNSAT */ }
            trace = s.solve();
        }
        traceDone();
    }

    private List<int[]> pendingClauses = null;
    private int pendingVars = 0;

    void setFormula(int numVars, List<int[]> clauses) {
        pendingVars = numVars;
        pendingClauses = clauses;
        solve();
    }

    private int stepCount() {
        return dpllMode
                ? (dpllSteps == null ? 0 : dpllSteps.size())
                : (trace == null ? 0 : trace.steps.size());
    }

    private void traceDone() {
        stepIdx = 0;
        prevLayout = null;
        prevTree = null;
        if (dpllMode) {
            curTree = GraphView.treeLayout(dpllSteps == null || dpllSteps.isEmpty()
                    ? null : dpllSteps.get(0));
            curLayout = null;
        } else {
            curLayout = GraphView.layout(trace == null || trace.steps.isEmpty()
                    ? null : trace.steps.get(0));
            curTree = null;
        }
        scrubber.setMaximum(Math.max(0, stepCount() - 1));
        scrubber.setValue(0);
        updatePanels();
        graphPanel.repaint();
    }

    void loadPreset(int idx) {
        switch (idx) {
            case 0 -> setFormula(6, List.of(
                    new int[]{1, 2}, new int[]{-1, 3}, new int[]{-1, 4},
                    new int[]{-3, -4}, new int[]{-2, 5}, new int[]{-2, 6},
                    new int[]{-5, -6}));
            case 1 -> setFormula(2, List.of(
                    new int[]{1, 2}, new int[]{-1, 2}, new int[]{1, -2}, new int[]{-1, -2}));
            case 2 -> {
                int pigeons = 3, holes = 2;
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
                setFormula(pigeons * holes, cls);
            }
            case 3 -> {
                // seed 11 from the preset sweep: 3 decisions, 3 conflicts, 3 learned clauses, UNSAT
                Random rng = new Random(11);
                int n = 8, m = (int) Math.round(n * 3.5);
                List<int[]> cls = new ArrayList<>();
                for (int i = 0; i < m; i++) {
                    int a = rng.nextInt(n) + 1, b = rng.nextInt(n) + 1, c = rng.nextInt(n) + 1;
                    cls.add(new int[]{rng.nextBoolean() ? a : -a,
                            rng.nextBoolean() ? b : -b,
                            rng.nextBoolean() ? c : -c});
                }
                setFormula(n, cls);
            }
            default -> { }
        }
    }

    void loadDimacs() {
        JFileChooser fc = new JFileChooser();
        if (fc.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) return;
        try {
            List<int[]> cls = new ArrayList<>();
            int nv = 0;
            for (String line : Files.readAllLines(fc.getSelectedFile().toPath())) {
                line = line.trim();
                if (line.isEmpty() || line.startsWith("c") || line.startsWith("p")) continue;
                String[] parts = line.split("\\s+");
                List<Integer> lits = new ArrayList<>();
                for (String p : parts) {
                    int v = Integer.parseInt(p);
                    if (v == 0) {
                        if (lits.isEmpty()) continue;
                        cls.add(lits.stream().mapToInt(Integer::intValue).toArray());
                        lits.clear();
                    } else {
                        nv = Math.max(nv, Math.abs(v));
                        lits.add(v);
                    }
                }
                if (!lits.isEmpty()) cls.add(lits.stream().mapToInt(Integer::intValue).toArray());
            }
            setFormula(nv, cls);
        } catch (Exception ex) {
            JOptionPane.showMessageDialog(this, "Could not read DIMACS: " + ex.getMessage());
        }
    }

    // ------------------------------------------------------------------
    void setStep(int i) {
        int n = stepCount();
        if (n == 0) return;
        i = Math.max(0, Math.min(n - 1, i));
        if (i == stepIdx && (curLayout != null || curTree != null)) return;
        prevLayout = curLayout;
        prevTree = curTree;
        stepIdx = i;
        if (dpllMode) {
            curTree = GraphView.treeLayout(dpllSteps.get(i));
        } else {
            curLayout = GraphView.layout(trace.steps.get(i));
        }
        stepTime = System.nanoTime();
        animTimer.start();
        updatePanels();
        if (!scrubber.getValueIsAdjusting()) scrubber.setValue(i);
    }

    void next() {
        if (stepCount() == 0) return;
        if (stepIdx >= stepCount() - 1) {
            if (playing) togglePlay();
            return;
        }
        setStep(stepIdx + 1);
    }

    void togglePlay() {
        playing = !playing;
        playBtn.setText(playing ? "⏸ Pause" : "▶ Play");
        if (playing) {
            if (stepIdx >= stepCount() - 1) setStep(0);
            playTimer.setDelay(Math.max(playDelayMs, 560));
            playTimer.start();
        } else {
            playTimer.stop();
        }
    }

    void onAnimTick() {
        double dt = (System.nanoTime() - stepTime) / 520_000_000.0;
        if (dt >= 1) { animTimer.stop(); dt = 1; }
        graphPanel.setAnim(dt);
    }

    private void updatePanels() {
        int n = stepCount();
        if (n == 0) return;
        String desc, note, verdict;
        if (dpllMode) {
            DpllSolver.Snapshot st = dpllSteps.get(stepIdx);
            infoArea.setText(String.format("step %d / %d   [%s]%n%n", stepIdx, n - 1, st.kind)
                    + st.desc
                    + (st.note == null || st.note.isEmpty() ? "" : String.format("%n%nℹ ") + st.note));
            // tree panel shows branch literal per node; trail shows current assignment
            StringBuilder tb = new StringBuilder();
            for (int[] pa : st.pathAssigns) {
                tb.append(String.format("x%-3d = %-5s%n", pa[0], pa[1] == 1 ? "T" : "F"));
            }
            trailArea.setText(tb.toString());
            trailArea.setCaretPosition(0);
            StringBuilder lb = new StringBuilder();
            for (DpllSolver.TNode tn : st.nodes) {
                String label = tn.kind == 'C' ? "conflict"
                        : (tn.lit < 0 ? "¬" : "") + "x" + Math.abs(tn.lit);
                if (tn.kind == 'C') {
                    lb.append("✗ ").append(label).append("  (dead end)\n");
                } else if (tn.status == DpllSolver.SAT) {
                    lb.append("✓ ").append(label).append("  (model leaf)\n");
                } else if (tn.status == DpllSolver.UNSAT) {
                    lb.append("✗ ").append(label)
                      .append(tn.kind == 'D' ? "  (subtree UNSAT)" : "  (falsified)").append("\n");
                }
            }
            learnedArea.setText(lb.toString());
            learnedArea.setCaretPosition(0);
            DpllSolver.Snapshot last = dpllSteps.get(n - 1);
            verdict = last.kind == Trace.Kind.SAT ? "SATISFIABLE"
                    : last.kind == Trace.Kind.UNSAT ? "UNSATISFIABLE" : "solving…";
        } else {
            Trace.Step st = trace.steps.get(stepIdx);
            infoArea.setText(String.format("step %d / %d   [%s]  level %d%n%n", stepIdx, n - 1,
                    st.kind, st.decisionLevel)
                    + st.desc
                    + (st.note == null || st.note.isEmpty() ? "" : "%n%nℹ " + st.note));
            StringBuilder sb = new StringBuilder();
            List<int[]> rows = st.learned;
            int start = Math.max(0, rows.size() - 200);
            for (int i = start; i < rows.size(); i++) {
                int[] row = rows.get(i);   // [id, learnt, lits...]
                if (row[1] != 1) continue;
                sb.append("c").append(row[0]).append(": ");
                if (row.length == 3) {
                    sb.append("⊥");
                } else {
                    for (int j = 2; j < row.length; j++) {
                        int l = row[j];
                        sb.append(j > 2 ? " ∨ " : "").append(l < 0 ? "¬" : "").append("x").append(Math.abs(l));
                    }
                }
                sb.append("\n");
            }
            learnedArea.setText(sb.toString());
            learnedArea.setCaretPosition(learnedArea.getDocument().getLength());

            StringBuilder tb = new StringBuilder();
            for (int[] r : st.trail) {
                tb.append(String.format("x%-3d = %-5s  level %-2d  %s%n", r[0], r[1] == 1 ? "T" : "F",
                        r[3], r[2] == -1 ? "decision / unit" : "reason c" + r[2]));
            }
            trailArea.setText(tb.toString());
            trailArea.setCaretPosition(0);

            Trace.Step last = trace.steps.get(trace.steps.size() - 1);
            verdict = last.kind == Trace.Kind.SAT ? "SATISFIABLE"
                    : last.kind == Trace.Kind.UNSAT ? "UNSATISFIABLE" : "solving…";
        }
        infoArea.setCaretPosition(0);
        stats.setText(" " + verdict + "  ");
        graphPanel.repaint();
    }

    // ------------------------------------------------------------------
    class GraphPanel extends JComponent {
        private double animT = 1;
        private double panX = 0, panY = 0, zoom = 1;
        private Point dragStart;

        void setAnim(double t) {
            animT = t;
            repaint();
        }

        GraphPanel() {
            setBackground(GraphView.BG);
            MouseAdapter mouse = new MouseAdapter() {
                public void mousePressed(MouseEvent e) { dragStart = e.getPoint(); }
                public void mouseDragged(MouseEvent e) {
                    if (dragStart != null) {
                        panX += e.getX() - dragStart.x;
                        panY += e.getY() - dragStart.y;
                        dragStart = e.getPoint();
                        repaint();
                    }
                }
                public void mouseWheelMoved(MouseWheelEvent e) {
                    double f = Math.pow(1.1, -e.getPreciseWheelRotation());
                    zoom = Math.max(0.3, Math.min(3, zoom * f));
                    repaint();
                }
                public void mouseClicked(MouseEvent e) {
                    panX = 0; panY = 0; zoom = 1; repaint();
                }
            };
            addMouseListener(mouse);
            addMouseMotionListener(mouse);
            addMouseWheelListener(mouse);
        }

        protected void paintComponent(Graphics g0) {
            Graphics2D g = (Graphics2D) g0.create();
            if (dpllMode) {
                DpllSolver.Snapshot cur = dpllSteps == null || dpllSteps.isEmpty()
                        ? null : dpllSteps.get(stepIdx);
                DpllSolver.Snapshot prev = dpllMode && stepIdx > 0 && prevTree != null
                        ? dpllSteps.get(stepIdx - 1) : null;
                GraphView.paintTree(g, getWidth(), getHeight(), cur, prev,
                        animT, curTree, prevTree, panX, panY, zoom,
                        stepIdx + 1, stepCount());
            } else {
                Trace.Step cur = trace == null || trace.steps.isEmpty() ? null : trace.steps.get(stepIdx);
                int learnedCount = cur == null ? 0 : (int) cur.learned.stream().filter(r -> r[1] == 1).count();
                GraphView.paint(g, getWidth(), getHeight(), cur,
                        stepIdx > 0 && prevLayout != null ? trace.steps.get(stepIdx - 1) : null,
                        animT, curLayout, prevLayout, panX, panY, zoom, learnedCount);
            }
            g.dispose();
        }
    }

    // ------------------------------------------------------------------
    public static void main(String[] args) throws Exception {
        String a0 = args.length > 0 ? args[0] : "";
        switch (a0) {
            case "--test" -> Test.main(args);
            case "--solve" -> solveHeadless(args.length > 1 ? args[1] : null);
            case "--render" -> Render.render(args.length > 1 ? args[1] : "/tmp/satviz_frames");
            default -> SwingUtilities.invokeLater(() -> new SatViz().setVisible(true));
        }
    }

    static void solveHeadless(String path) throws Exception {
        List<int[]> cls = new ArrayList<>();
        int nv = 0;
        for (String line : Files.readAllLines(Path.of(path))) {
            line = line.trim();
            if (line.isEmpty() || line.startsWith("c") || line.startsWith("p")) continue;
            List<Integer> lits = new ArrayList<>();
            for (String p : line.split("\\s+")) {
                int v = Integer.parseInt(p);
                if (v == 0) {
                    if (!lits.isEmpty()) { cls.add(lits.stream().mapToInt(Integer::intValue).toArray()); lits.clear(); }
                } else { nv = Math.max(nv, Math.abs(v)); lits.add(v); }
            }
            if (!lits.isEmpty()) cls.add(lits.stream().mapToInt(Integer::intValue).toArray());
        }
        Solver s = new Solver(nv);
        boolean trivial = false;
        for (int[] c : cls) if (!s.addClause(c.clone())) trivial = true;
        Trace t = trivial ? null : s.solve();
        boolean sat = t != null && t.steps.get(t.steps.size() - 1).kind == Trace.Kind.SAT;
        System.out.println(sat ? "s SATISFIABLE" : "s UNSATISFIABLE");
        System.exit(sat ? 10 : 20);
    }
}
