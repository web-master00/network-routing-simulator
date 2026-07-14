/*
# Dynamic Network Packet Routing Engine

## What it is

A graph-theory network simulation that applies dynamic cost adjustments to
pathfinding matrices under thread-isolated data streaming conditions:

- **Custom adjacency matrices** - Vertices are routers and edges are physical
  links with latency/bandwidth weights supplied at runtime (no hardcoded topology).
- **Thread-safe Dijkstra** - Shortest paths are recomputed against a live cost
  matrix protected by a read/write lock so concurrent hop workers never race.
- **Congestion-aware rerouting** - Each router tracks buffer occupancy; when
  utilization exceeds a parameterized threshold, incident link costs rise in
  real time and subsequent packets recalculate through less congested routers.
- **Message-queue packet stream** - High-volume discrete packets move through a
  `BlockingQueue` driven by virtual-thread workers while a Swing canvas animates
  hops without blocking the EDT.

## What it is used for

Software-Defined Networking (SDN) controllers, BGP/OSPF telecom routing
infrastructure, and telemetry tracking in distributed cloud systems:

- **SDN controllers** - Prototype reactive path selection when fabric buffers
  saturate and link costs must change without tearing down the data plane.
- **BGP/OSPF-style infrastructure** - Illustrate how elevated path costs steer
  traffic away from congested hops while streams continue.
- **Cloud telemetry** - Visualize live buffer pressure (green → red) and packet
  flows for operations dashboards and what-if congestion drills.

Compile and run (JDK 21+):

    javac NetworkRoutingSimulator.java
    java NetworkRoutingSimulator --nodes 8 --rate 40 --buffer 32 --threshold 0.7
*/

import java.awt.BasicStroke;
import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.RenderingHints;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Line2D;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Locale;
import java.util.Objects;
import java.util.PriorityQueue;
import java.util.Random;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSpinner;
import javax.swing.JTextArea;
import javax.swing.SpinnerNumberModel;
import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;
import javax.swing.Timer;
import javax.swing.UIManager;
import javax.swing.WindowConstants;
import javax.swing.border.EmptyBorder;

/**
 * Self-contained Dynamic Network Packet Routing Engine with congestion-aware
 * Dijkstra rerouting, BlockingQueue packet streaming, and a live Swing canvas.
 */
public class NetworkRoutingSimulator {

    // -------------------------------------------------------------------------
    // Immutable / parameterized domain models
    // -------------------------------------------------------------------------

    /**
     * Fully parameterized simulation knobs. Defaults live only here so runtime
     * logic never embeds magic limits.
     */
    public record SimulationConfig(
            int nodeCount,
            int workerThreads,
            int packetsPerSecond,
            int bufferCapacity,
            double congestionThreshold,
            double congestionMultiplier,
            int sourceNode,
            int destinationNode,
            long hopMillis
    ) {
        public static final SimulationConfig DEFAULTS = new SimulationConfig(
                8,
                8,
                40,
                32,
                0.70,
                4.0,
                0,
                4,
                180L
        );

        public SimulationConfig {
            if (nodeCount < 2) {
                throw new IllegalArgumentException("nodeCount must be >= 2");
            }
            if (workerThreads < 1) {
                throw new IllegalArgumentException("workerThreads must be >= 1");
            }
            if (packetsPerSecond < 1) {
                throw new IllegalArgumentException("packetsPerSecond must be >= 1");
            }
            if (bufferCapacity < 1) {
                throw new IllegalArgumentException("bufferCapacity must be >= 1");
            }
            if (congestionThreshold <= 0.0 || congestionThreshold > 1.0) {
                throw new IllegalArgumentException("congestionThreshold must be in (0, 1]");
            }
            if (congestionMultiplier < 1.0) {
                throw new IllegalArgumentException("congestionMultiplier must be >= 1");
            }
            if (sourceNode < 0 || sourceNode >= nodeCount) {
                throw new IllegalArgumentException("sourceNode out of range");
            }
            if (destinationNode < 0 || destinationNode >= nodeCount) {
                throw new IllegalArgumentException("destinationNode out of range");
            }
            if (sourceNode == destinationNode) {
                throw new IllegalArgumentException("source and destination must differ");
            }
            if (hopMillis < 20L) {
                throw new IllegalArgumentException("hopMillis must be >= 20");
            }
        }
    }

    /** Mutable in-flight packet with animation progress along the current hop. */
    static final class Packet {
        final long id;
        final int source;
        final int destination;
        final Color color;
        volatile List<Integer> path;
        volatile int hopIndex;
        /** Fractional progress along the edge from path[hopIndex] → path[hopIndex+1]. */
        volatile double progress;
        volatile boolean delivered;
        volatile boolean dropped;

        Packet(long id, int source, int destination, List<Integer> path, Color color) {
            this.id = id;
            this.source = source;
            this.destination = destination;
            this.path = List.copyOf(path);
            this.hopIndex = 0;
            this.progress = 0.0;
            this.color = color;
        }

        boolean hasNextHop() {
            List<Integer> p = path;
            return hopIndex + 1 < p.size();
        }

        int currentNode() {
            return path.get(hopIndex);
        }

        int nextNode() {
            return path.get(hopIndex + 1);
        }
    }

    /** Per-router buffer state exposed to the engine and canvas. */
    static final class RouterNode {
        final int id;
        final int capacity;
        final AtomicInteger bufferOccupancy = new AtomicInteger(0);
        volatile double layoutX;
        volatile double layoutY;

        RouterNode(int id, int capacity) {
            this.id = id;
            this.capacity = capacity;
        }

        double utilization() {
            return Math.min(1.0, bufferOccupancy.get() / (double) capacity);
        }

        boolean tryOccupy() {
            while (true) {
                int current = bufferOccupancy.get();
                if (current >= capacity) {
                    return false;
                }
                if (bufferOccupancy.compareAndSet(current, current + 1)) {
                    return true;
                }
            }
        }

        void release() {
            bufferOccupancy.updateAndGet(v -> Math.max(0, v - 1));
        }
    }

    // -------------------------------------------------------------------------
    // Graph + pathfinding
    // -------------------------------------------------------------------------

    /**
     * Weighted undirected/directed adjacency with a live cost overlay that
     * rises when endpoint buffers cross the congestion threshold.
     */
    static final class NetworkGraph {
        private final int n;
        private final double[][] baseWeights;
        private final double[][] liveCosts;
        private final RouterNode[] routers;
        private final double congestionThreshold;
        private final double congestionMultiplier;
        private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        private final boolean[] congested;

        NetworkGraph(
                double[][] adjacency,
                int bufferCapacity,
                double congestionThreshold,
                double congestionMultiplier
        ) {
            Objects.requireNonNull(adjacency, "adjacency");
            this.n = adjacency.length;
            if (n < 2) {
                throw new IllegalArgumentException("graph must have at least 2 nodes");
            }
            for (double[] row : adjacency) {
                if (row == null || row.length != n) {
                    throw new IllegalArgumentException("adjacency must be a square matrix");
                }
            }
            this.baseWeights = deepCopy(adjacency);
            this.liveCosts = deepCopy(adjacency);
            this.congestionThreshold = congestionThreshold;
            this.congestionMultiplier = congestionMultiplier;
            this.congested = new boolean[n];
            this.routers = new RouterNode[n];
            for (int i = 0; i < n; i++) {
                routers[i] = new RouterNode(i, bufferCapacity);
            }
            layoutCircle(n);
        }

        int size() {
            return n;
        }

        RouterNode router(int id) {
            return routers[id];
        }

        RouterNode[] routers() {
            return routers;
        }

        double baseWeight(int from, int to) {
            return baseWeights[from][to];
        }

        boolean hasEdge(int from, int to) {
            return from != to && baseWeights[from][to] > 0.0 && !Double.isInfinite(baseWeights[from][to]);
        }

        /** Snapshot of live costs for pathfinding / drawing. */
        double[][] snapshotLiveCosts() {
            lock.readLock().lock();
            try {
                return deepCopy(liveCosts);
            } finally {
                lock.readLock().unlock();
            }
        }

        double liveCost(int from, int to) {
            lock.readLock().lock();
            try {
                return liveCosts[from][to];
            } finally {
                lock.readLock().unlock();
            }
        }

        /**
         * Recompute live costs from base weights and current buffer utilization.
         * Called after every buffer occupy/release.
         */
        void refreshCostsFromBuffers() {
            lock.writeLock().lock();
            try {
                for (int i = 0; i < n; i++) {
                    congested[i] = routers[i].utilization() >= congestionThreshold;
                }
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        double base = baseWeights[i][j];
                        if (i == j || base <= 0.0 || Double.isInfinite(base)) {
                            liveCosts[i][j] = base <= 0.0 ? 0.0 : base;
                            continue;
                        }
                        double cost = base;
                        if (congested[i] || congested[j]) {
                            cost *= congestionMultiplier;
                        }
                        liveCosts[i][j] = cost;
                    }
                }
            } finally {
                lock.writeLock().unlock();
            }
        }

        void layoutCircle(int count) {
            double cx = 0.5;
            double cy = 0.5;
            double radius = 0.38;
            for (int i = 0; i < count; i++) {
                double angle = (2.0 * Math.PI * i / count) - Math.PI / 2.0;
                routers[i].layoutX = cx + radius * Math.cos(angle);
                routers[i].layoutY = cy + radius * Math.sin(angle);
            }
        }

        static double[][] deepCopy(double[][] src) {
            double[][] copy = new double[src.length][];
            for (int i = 0; i < src.length; i++) {
                copy[i] = Arrays.copyOf(src[i], src[i].length);
            }
            return copy;
        }

        /**
         * Build a connected mesh with heterogeneous weights as a UI/CLI starting
         * template only - runtime pathfinding never embeds this topology.
         */
        static double[][] sampleMesh(int nodes, long seed) {
            if (nodes < 2) {
                throw new IllegalArgumentException("nodes must be >= 2");
            }
            Random rng = new Random(seed);
            double[][] m = new double[nodes][nodes];
            for (int i = 0; i < nodes; i++) {
                Arrays.fill(m[i], 0.0);
            }
            // Ring backbone
            for (int i = 0; i < nodes; i++) {
                int j = (i + 1) % nodes;
                double w = 1.0 + rng.nextDouble() * 4.0;
                m[i][j] = w;
                m[j][i] = w;
            }
            // Skip-one chords create alternate multi-hop corridors
            for (int i = 0; i < nodes; i++) {
                int j = (i + 2) % nodes;
                if (m[i][j] == 0.0) {
                    double w = 2.0 + rng.nextDouble() * 6.0;
                    m[i][j] = w;
                    m[j][i] = w;
                }
            }
            // Occasional longer chords (avoid guaranteeing a cheap diametric shortcut)
            if (nodes >= 6) {
                for (int i = 0; i < nodes; i++) {
                    int j = (i + 3) % nodes;
                    if (i < j && m[i][j] == 0.0 && rng.nextDouble() < 0.45) {
                        double w = 4.0 + rng.nextDouble() * 9.0;
                        m[i][j] = w;
                        m[j][i] = w;
                    }
                }
            }
            return m;
        }

        /** Parse whitespace/comma-separated square matrix text. */
        static double[][] parseMatrix(String text) {
            Objects.requireNonNull(text, "text");
            String[] lines = text.trim().split("\\R+");
            List<double[]> rows = new ArrayList<>();
            for (String line : lines) {
                String trimmed = line.trim();
                if (trimmed.isEmpty() || trimmed.startsWith("#")) {
                    continue;
                }
                String[] tokens = trimmed.split("[,\\s]+");
                double[] row = new double[tokens.length];
                for (int i = 0; i < tokens.length; i++) {
                    String token = tokens[i].trim();
                    if (token.equalsIgnoreCase("inf") || token.equals("-")) {
                        row[i] = 0.0;
                    } else {
                        row[i] = Double.parseDouble(token);
                        if (row[i] < 0.0) {
                            throw new IllegalArgumentException("edge weights must be >= 0");
                        }
                    }
                }
                rows.add(row);
            }
            if (rows.isEmpty()) {
                throw new IllegalArgumentException("matrix is empty");
            }
            int n = rows.size();
            double[][] matrix = new double[n][n];
            for (int i = 0; i < n; i++) {
                if (rows.get(i).length != n) {
                    throw new IllegalArgumentException(
                            "row " + i + " has length " + rows.get(i).length + ", expected " + n
                    );
                }
                matrix[i] = rows.get(i);
            }
            return matrix;
        }

        static String formatMatrix(double[][] matrix) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < matrix.length; i++) {
                for (int j = 0; j < matrix[i].length; j++) {
                    if (j > 0) {
                        sb.append(' ');
                    }
                    double v = matrix[i][j];
                    if (v == 0.0) {
                        sb.append('0');
                    } else if (Math.rint(v) == v) {
                        sb.append((int) v);
                    } else {
                        sb.append(String.format(Locale.US, "%.2f", v));
                    }
                }
                if (i + 1 < matrix.length) {
                    sb.append('\n');
                }
            }
            return sb.toString();
        }
    }

    /** Thread-safe Dijkstra over the live cost matrix. */
    static final class Pathfinder {
        private Pathfinder() {
        }

        static List<Integer> shortestPath(NetworkGraph graph, int source, int destination) {
            int n = graph.size();
            if (source < 0 || source >= n || destination < 0 || destination >= n) {
                return List.of();
            }
            if (source == destination) {
                return List.of(source);
            }

            double[][] costs = graph.snapshotLiveCosts();
            double[] dist = new double[n];
            int[] prev = new int[n];
            boolean[] visited = new boolean[n];
            Arrays.fill(dist, Double.POSITIVE_INFINITY);
            Arrays.fill(prev, -1);
            dist[source] = 0.0;

            record NodeDist(int node, double distance) {
            }
            PriorityQueue<NodeDist> heap = new PriorityQueue<>((a, b) -> Double.compare(a.distance, b.distance));
            heap.offer(new NodeDist(source, 0.0));

            while (!heap.isEmpty()) {
                NodeDist current = heap.poll();
                int u = current.node;
                if (visited[u]) {
                    continue;
                }
                visited[u] = true;
                if (u == destination) {
                    break;
                }
                for (int v = 0; v < n; v++) {
                    double w = costs[u][v];
                    if (u == v || w <= 0.0 || Double.isInfinite(w) || visited[v]) {
                        continue;
                    }
                    double candidate = dist[u] + w;
                    if (candidate < dist[v]) {
                        dist[v] = candidate;
                        prev[v] = u;
                        heap.offer(new NodeDist(v, candidate));
                    }
                }
            }

            if (prev[destination] < 0 && source != destination) {
                return List.of();
            }

            List<Integer> path = new ArrayList<>();
            for (int at = destination; at != -1; at = prev[at]) {
                path.add(at);
                if (at == source) {
                    break;
                }
            }
            if (path.isEmpty() || path.get(path.size() - 1) != source) {
                return List.of();
            }
            Collections.reverse(path);
            return List.copyOf(path);
        }
    }

    // -------------------------------------------------------------------------
    // Concurrent routing engine
    // -------------------------------------------------------------------------

    enum UiEventType {
        PACKET_DELIVERED,
        PACKET_DROPPED,
        STATS
    }

    record UiEvent(
            UiEventType type,
            long delivered,
            long dropped,
            long inFlight,
            double packetsPerSecond,
            String message
    ) {
    }

    static final class RoutingEngine {
        private final SimulationConfig config;
        private final NetworkGraph graph;
        private final BlockingQueue<Packet> hopQueue = new LinkedBlockingQueue<>();
        private final List<Packet> activePackets = Collections.synchronizedList(new ArrayList<>());
        private final AtomicBoolean running = new AtomicBoolean(false);
        private final AtomicLong packetIdSeq = new AtomicLong(0);
        private final LongAdder delivered = new LongAdder();
        private final LongAdder dropped = new LongAdder();
        private final AtomicLong hopCountTotal = new AtomicLong(0);

        private ExecutorService executor;
        private Future<?> injectorFuture;
        private final List<Future<?>> workerFutures = new ArrayList<>();
        private long startedAtNanos;

        RoutingEngine(SimulationConfig config, NetworkGraph graph) {
            this.config = config;
            this.graph = graph;
        }

        NetworkGraph graph() {
            return graph;
        }

        SimulationConfig config() {
            return config;
        }

        List<Packet> snapshotActivePackets() {
            synchronized (activePackets) {
                return List.copyOf(activePackets);
            }
        }

        long deliveredCount() {
            return delivered.sum();
        }

        long droppedCount() {
            return dropped.sum();
        }

        int inFlightCount() {
            return activePackets.size();
        }

        double deliveredPerSecond() {
            long elapsed = System.nanoTime() - startedAtNanos;
            if (elapsed <= 0L) {
                return 0.0;
            }
            return delivered.sum() / (elapsed / 1_000_000_000.0);
        }

        double averageHops() {
            long d = delivered.sum();
            if (d == 0L) {
                return 0.0;
            }
            return hopCountTotal.get() / (double) d;
        }

        void start() {
            if (!running.compareAndSet(false, true)) {
                return;
            }
            startedAtNanos = System.nanoTime();
            delivered.reset();
            dropped.reset();
            hopCountTotal.set(0);
            hopQueue.clear();
            activePackets.clear();
            for (RouterNode node : graph.routers()) {
                node.bufferOccupancy.set(0);
            }
            graph.refreshCostsFromBuffers();

            executor = Executors.newThreadPerTaskExecutor(Thread.ofVirtual().name("route-", 0).factory());
            injectorFuture = executor.submit(this::injectLoop);
            workerFutures.clear();
            for (int i = 0; i < config.workerThreads(); i++) {
                workerFutures.add(executor.submit(this::hopWorkerLoop));
            }
        }

        void stop() {
            running.set(false);
            if (injectorFuture != null) {
                injectorFuture.cancel(true);
            }
            for (Future<?> f : workerFutures) {
                f.cancel(true);
            }
            if (executor != null) {
                executor.shutdownNow();
                try {
                    executor.awaitTermination(2, TimeUnit.SECONDS);
                } catch (InterruptedException ie) {
                    Thread.currentThread().interrupt();
                }
            }
            hopQueue.clear();
            synchronized (activePackets) {
                for (Packet p : activePackets) {
                    if (!p.delivered && !p.dropped) {
                        releaseCurrentBuffer(p);
                    }
                }
                activePackets.clear();
            }
            for (RouterNode node : graph.routers()) {
                node.bufferOccupancy.set(0);
            }
            graph.refreshCostsFromBuffers();
        }

        boolean isRunning() {
            return running.get();
        }

        private void injectLoop() {
            long intervalNanos = Math.max(1_000_000L, 1_000_000_000L / config.packetsPerSecond());
            try {
                while (running.get()) {
                    injectOne();
                    TimeUnit.NANOSECONDS.sleep(intervalNanos);
                }
            } catch (InterruptedException ie) {
                Thread.currentThread().interrupt();
            }
        }

        private void injectOne() {
            List<Integer> path = Pathfinder.shortestPath(graph, config.sourceNode(), config.destinationNode());
            if (path.isEmpty() || path.size() < 2) {
                dropped.increment();
                return;
            }
            RouterNode sourceRouter = graph.router(config.sourceNode());
            if (!sourceRouter.tryOccupy()) {
                dropped.increment();
                graph.refreshCostsFromBuffers();
                return;
            }
            graph.refreshCostsFromBuffers();

            long id = packetIdSeq.incrementAndGet();
            Color color = packetColor(id);
            Packet packet = new Packet(id, config.sourceNode(), config.destinationNode(), path, color);
            activePackets.add(packet);
            hopQueue.offer(packet);
        }

        private void hopWorkerLoop() {
            try {
                while (running.get()) {
                    Packet packet = hopQueue.poll(100, TimeUnit.MILLISECONDS);
                    if (packet == null) {
                        continue;
                    }
                    processHop(packet);
                }
            } catch (InterruptedException ie) {
                Thread.currentThread().interrupt();
            }
        }

        private void processHop(Packet packet) throws InterruptedException {
            if (!running.get() || packet.delivered || packet.dropped) {
                return;
            }
            if (!packet.hasNextHop()) {
                // Already sitting in the destination buffer - linger so occupancy is visible.
                dwellAtNode();
                if (running.get()) {
                    completeDelivery(packet);
                }
                return;
            }

            int from = packet.currentNode();
            int to = packet.nextNode();

            // Reserve the receiving router's buffer before transit so packets
            // visible on an inbound edge count against the destination node.
            RouterNode nextRouter = graph.router(to);
            if (!nextRouter.tryOccupy()) {
                graph.refreshCostsFromBuffers();
                List<Integer> recalc = Pathfinder.shortestPath(graph, from, packet.destination);
                if (recalc.isEmpty() || recalc.size() < 2) {
                    dropPacket(packet);
                    return;
                }
                packet.path = List.copyOf(recalc);
                packet.hopIndex = 0;
                packet.progress = 0.0;
                graph.refreshCostsFromBuffers();
                hopQueue.offer(packet);
                return;
            }

            graph.router(from).release();
            graph.refreshCostsFromBuffers();

            // Smooth animation along the edge while occupying the receiver.
            long hopMs = config.hopMillis();
            long steps = Math.max(8, hopMs / 16);
            for (long s = 1; s <= steps && running.get(); s++) {
                packet.progress = s / (double) steps;
                TimeUnit.MILLISECONDS.sleep(hopMs / steps);
            }
            if (!running.get()) {
                return;
            }

            packet.hopIndex++;
            packet.progress = 0.0;

            if (packet.currentNode() == packet.destination || !packet.hasNextHop()) {
                dwellAtNode();
                if (running.get()) {
                    completeDelivery(packet);
                }
            } else {
                // Mid-path dynamic recalculation when current node is congested
                if (graph.router(packet.currentNode()).utilization() >= config.congestionThreshold()) {
                    List<Integer> alt = Pathfinder.shortestPath(
                            graph,
                            packet.currentNode(),
                            packet.destination
                    );
                    if (!alt.isEmpty() && alt.size() >= 2) {
                        packet.path = List.copyOf(alt);
                        packet.hopIndex = 0;
                        packet.progress = 0.0;
                    }
                }
                hopQueue.offer(packet);
            }
        }

        /** Hold a packet on its current router so buffer heat is observable in the UI. */
        private void dwellAtNode() throws InterruptedException {
            long dwellMs = Math.max(60L, config.hopMillis() / 2);
            TimeUnit.MILLISECONDS.sleep(dwellMs);
        }

        private void completeDelivery(Packet packet) {
            releaseCurrentBuffer(packet);
            packet.delivered = true;
            packet.progress = 1.0;
            hopCountTotal.addAndGet(Math.max(0, packet.path.size() - 1));
            delivered.increment();
            activePackets.remove(packet);
            graph.refreshCostsFromBuffers();
        }

        private void dropPacket(Packet packet) {
            releaseCurrentBuffer(packet);
            packet.dropped = true;
            dropped.increment();
            activePackets.remove(packet);
            graph.refreshCostsFromBuffers();
        }

        private void releaseCurrentBuffer(Packet packet) {
            try {
                if (packet.hopIndex < packet.path.size()) {
                    graph.router(packet.currentNode()).release();
                }
            } catch (RuntimeException ignored) {
                // Path may already be cleared during shutdown.
            }
        }

        private static Color packetColor(long id) {
            float hue = (id * 0.6180339887f) % 1.0f;
            return Color.getHSBColor(hue, 0.75f, 0.95f);
        }
    }

    // -------------------------------------------------------------------------
    // SwingWorker bridge
    // -------------------------------------------------------------------------

    static final class SimulationWorker extends SwingWorker<Void, UiEvent> {
        private final RoutingEngine engine;
        private final NetworkCanvas canvas;
        private final JLabel ppsLabel;
        private final JLabel deliveredLabel;
        private final JLabel droppedLabel;
        private final JLabel inFlightLabel;
        private final JLabel avgHopsLabel;
        private final JLabel statusLabel;
        private final Runnable onFinished;
        private final AtomicBoolean stopRequested = new AtomicBoolean(false);

        SimulationWorker(
                RoutingEngine engine,
                NetworkCanvas canvas,
                JLabel ppsLabel,
                JLabel deliveredLabel,
                JLabel droppedLabel,
                JLabel inFlightLabel,
                JLabel avgHopsLabel,
                JLabel statusLabel,
                Runnable onFinished
        ) {
            this.engine = engine;
            this.canvas = canvas;
            this.ppsLabel = ppsLabel;
            this.deliveredLabel = deliveredLabel;
            this.droppedLabel = droppedLabel;
            this.inFlightLabel = inFlightLabel;
            this.avgHopsLabel = avgHopsLabel;
            this.statusLabel = statusLabel;
            this.onFinished = onFinished;
        }

        void requestStop() {
            stopRequested.set(true);
            engine.stop();
        }

        @Override
        protected Void doInBackground() {
            engine.start();
            canvas.bindEngine(engine);
            try {
                while (!stopRequested.get() && engine.isRunning() && !isCancelled()) {
                    publish(new UiEvent(
                            UiEventType.STATS,
                            engine.deliveredCount(),
                            engine.droppedCount(),
                            engine.inFlightCount(),
                            engine.deliveredPerSecond(),
                            null
                    ));
                    TimeUnit.MILLISECONDS.sleep(200);
                }
            } catch (InterruptedException ie) {
                Thread.currentThread().interrupt();
            } finally {
                engine.stop();
            }
            return null;
        }

        @Override
        protected void process(List<UiEvent> chunks) {
            if (chunks.isEmpty()) {
                return;
            }
            UiEvent last = chunks.get(chunks.size() - 1);
            ppsLabel.setText(String.format(Locale.US, "%.1f", last.packetsPerSecond()));
            deliveredLabel.setText(Long.toString(last.delivered()));
            droppedLabel.setText(Long.toString(last.dropped()));
            inFlightLabel.setText(Long.toString(last.inFlight()));
            avgHopsLabel.setText(String.format(Locale.US, "%.2f", engine.averageHops()));
        }

        @Override
        protected void done() {
            canvas.bindEngine(null);
            statusLabel.setText("Stopped");
            onFinished.run();
        }
    }

    // -------------------------------------------------------------------------
    // Visualization canvas
    // -------------------------------------------------------------------------

    static final class NetworkCanvas extends JPanel {
        private static final Color BG_TOP = new Color(0x0F1A24);
        private static final Color BG_BOTTOM = new Color(0x1A2E3D);
        private static final Color EDGE_BASE = new Color(0x5A7A8C);
        private static final Color EDGE_HOT = new Color(0xC44B2B);
        private static final Color NODE_RING = new Color(0xE8F0F4);
        private static final Color LABEL = new Color(0xF2F7FA);
        private static final Color GREEN = new Color(0x8FDB6E);
        private static final Color RED = new Color(0x8B1A1A);

        private NetworkGraph graph;
        private RoutingEngine engine;
        private final Timer repaintTimer;

        NetworkCanvas() {
            setPreferredSize(new Dimension(720, 520));
            setBackground(BG_BOTTOM);
            repaintTimer = new Timer(33, e -> repaint());
            repaintTimer.start();
        }

        void setGraph(NetworkGraph graph) {
            this.graph = graph;
            repaint();
        }

        void bindEngine(RoutingEngine engine) {
            this.engine = engine;
            if (engine != null) {
                this.graph = engine.graph();
            }
        }

        void disposeTimer() {
            repaintTimer.stop();
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            Graphics2D g2 = (Graphics2D) g.create();
            try {
                g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
                fillBackground(g2);
                if (graph == null) {
                    g2.setColor(LABEL);
                    g2.drawString("Load an adjacency matrix to render the network.", 24, 32);
                    return;
                }
                int w = getWidth();
                int h = getHeight();
                int n = graph.size();

                // Edges
                for (int i = 0; i < n; i++) {
                    for (int j = i + 1; j < n; j++) {
                        if (!graph.hasEdge(i, j) && !graph.hasEdge(j, i)) {
                            continue;
                        }
                        double cost = Math.max(graph.liveCost(i, j), graph.liveCost(j, i));
                        double base = Math.max(graph.baseWeight(i, j), graph.baseWeight(j, i));
                        float congestionRatio = base > 0 ? (float) Math.min(1.0, (cost / base - 1.0) / 3.0) : 0f;
                        Color edgeColor = lerpColor(EDGE_BASE, EDGE_HOT, Math.max(0f, congestionRatio));
                        float stroke = 1.5f + congestionRatio * 3.5f;
                        g2.setStroke(new BasicStroke(stroke));
                        g2.setColor(edgeColor);
                        double x1 = graph.router(i).layoutX * w;
                        double y1 = graph.router(i).layoutY * h;
                        double x2 = graph.router(j).layoutX * w;
                        double y2 = graph.router(j).layoutY * h;
                        g2.draw(new Line2D.Double(x1, y1, x2, y2));
                    }
                }

                // Packets
                if (engine != null) {
                    for (Packet packet : engine.snapshotActivePackets()) {
                        if (packet.delivered || packet.dropped) {
                            continue;
                        }
                        List<Integer> path = packet.path;
                        if (path == null || path.size() < 2 || packet.hopIndex + 1 >= path.size()) {
                            drawPacketDot(g2, graph.router(packet.currentNode()), w, h, packet.color);
                            continue;
                        }
                        RouterNode a = graph.router(path.get(packet.hopIndex));
                        RouterNode b = graph.router(path.get(packet.hopIndex + 1));
                        double t = packet.progress;
                        double px = (a.layoutX + (b.layoutX - a.layoutX) * t) * w;
                        double py = (a.layoutY + (b.layoutY - a.layoutY) * t) * h;
                        g2.setColor(packet.color);
                        g2.fill(new Ellipse2D.Double(px - 5, py - 5, 10, 10));
                        g2.setColor(Color.WHITE);
                        g2.setStroke(new BasicStroke(1f));
                        g2.draw(new Ellipse2D.Double(px - 5, py - 5, 10, 10));
                    }
                }

                // Routers
                for (int i = 0; i < n; i++) {
                    RouterNode node = graph.router(i);
                    double util = node.utilization();
                    Color fill = lerpColor(GREEN, RED, (float) util);
                    double cx = node.layoutX * w;
                    double cy = node.layoutY * h;
                    double r = 18;
                    g2.setColor(fill);
                    g2.fill(new Ellipse2D.Double(cx - r, cy - r, r * 2, r * 2));
                    g2.setColor(NODE_RING);
                    g2.setStroke(new BasicStroke(2f));
                    g2.draw(new Ellipse2D.Double(cx - r, cy - r, r * 2, r * 2));
                    g2.setColor(LABEL);
                    g2.setFont(getFont().deriveFont(Font.BOLD, 12f));
                    String label = "R" + i;
                    int tw = g2.getFontMetrics().stringWidth(label);
                    g2.drawString(label, (float) (cx - tw / 2.0), (float) (cy + 4));
                    g2.setFont(getFont().deriveFont(10f));
                    String buf = node.bufferOccupancy.get() + "/" + node.capacity;
                    int bw = g2.getFontMetrics().stringWidth(buf);
                    g2.drawString(buf, (float) (cx - bw / 2.0), (float) (cy + r + 12));
                }
            } finally {
                g2.dispose();
            }
        }

        private void drawPacketDot(Graphics2D g2, RouterNode node, int w, int h, Color color) {
            double px = node.layoutX * w;
            double py = node.layoutY * h;
            g2.setColor(color);
            g2.fill(new Ellipse2D.Double(px - 5, py - 5, 10, 10));
        }

        private void fillBackground(Graphics2D g2) {
            int h = getHeight();
            for (int y = 0; y < h; y++) {
                float t = h <= 1 ? 0f : y / (float) (h - 1);
                g2.setColor(lerpColor(BG_TOP, BG_BOTTOM, t));
                g2.drawLine(0, y, getWidth(), y);
            }
        }

        private static Color lerpColor(Color a, Color b, float t) {
            t = Math.max(0f, Math.min(1f, t));
            int r = (int) (a.getRed() + (b.getRed() - a.getRed()) * t);
            int g = (int) (a.getGreen() + (b.getGreen() - a.getGreen()) * t);
            int bl = (int) (a.getBlue() + (b.getBlue() - a.getBlue()) * t);
            return new Color(r, g, bl);
        }
    }

    // -------------------------------------------------------------------------
    // Main window
    // -------------------------------------------------------------------------

    static final class RoutingFrame extends JFrame {
        private final JSpinner nodesSpinner;
        private final JSpinner threadsSpinner;
        private final JSpinner rateSpinner;
        private final JSpinner bufferSpinner;
        private final JSpinner thresholdSpinner;
        private final JSpinner multiplierSpinner;
        private final JSpinner sourceSpinner;
        private final JSpinner destSpinner;
        private final JTextArea matrixArea;
        private final JLabel ppsLabel = metricValue("0.0");
        private final JLabel deliveredLabel = metricValue("0");
        private final JLabel droppedLabel = metricValue("0");
        private final JLabel inFlightLabel = metricValue("0");
        private final JLabel avgHopsLabel = metricValue("0.00");
        private final JLabel statusLabel = new JLabel("Ready");
        private final JButton startButton = new JButton("Start");
        private final JButton stopButton = new JButton("Stop");
        private final JButton applyMatrixButton = new JButton("Apply Matrix");
        private final JButton sampleButton = new JButton("Sample Mesh");
        private final NetworkCanvas canvas = new NetworkCanvas();
        private final SimulationConfig initialConfig;

        private SimulationWorker worker;
        private RoutingEngine engine;
        private NetworkGraph previewGraph;

        RoutingFrame(SimulationConfig config) {
            super("Dynamic Network Packet Routing Engine");
            this.initialConfig = config;

            nodesSpinner = new JSpinner(new SpinnerNumberModel(config.nodeCount(), 2, 48, 1));
            threadsSpinner = new JSpinner(new SpinnerNumberModel(config.workerThreads(), 1, 128, 1));
            rateSpinner = new JSpinner(new SpinnerNumberModel(config.packetsPerSecond(), 1, 500, 1));
            bufferSpinner = new JSpinner(new SpinnerNumberModel(config.bufferCapacity(), 1, 512, 1));
            thresholdSpinner = new JSpinner(new SpinnerNumberModel(config.congestionThreshold(), 0.1, 1.0, 0.05));
            multiplierSpinner = new JSpinner(new SpinnerNumberModel(config.congestionMultiplier(), 1.0, 20.0, 0.5));
            sourceSpinner = new JSpinner(new SpinnerNumberModel(config.sourceNode(), 0, config.nodeCount() - 1, 1));
            destSpinner = new JSpinner(new SpinnerNumberModel(config.destinationNode(), 0, config.nodeCount() - 1, 1));

            double[][] sample = NetworkGraph.sampleMesh(config.nodeCount(), 42L);
            matrixArea = new JTextArea(NetworkGraph.formatMatrix(sample), 8, 28);
            matrixArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
            previewGraph = new NetworkGraph(
                    sample,
                    config.bufferCapacity(),
                    config.congestionThreshold(),
                    config.congestionMultiplier()
            );
            canvas.setGraph(previewGraph);

            setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            setLayout(new BorderLayout(8, 8));
            ((JPanel) getContentPane()).setBorder(new EmptyBorder(10, 10, 10, 10));

            add(buildControls(), BorderLayout.NORTH);
            add(buildCenter(), BorderLayout.CENTER);
            add(buildScoreboard(), BorderLayout.SOUTH);

            stopButton.setEnabled(false);
            startButton.addActionListener(e -> startSimulation());
            stopButton.addActionListener(e -> stopSimulation());
            applyMatrixButton.addActionListener(e -> applyMatrixPreview());
            sampleButton.addActionListener(e -> loadSampleMesh());
            nodesSpinner.addChangeListener(e -> syncNodeSpinners());

            addWindowListener(new WindowAdapter() {
                @Override
                public void windowClosing(WindowEvent e) {
                    stopSimulation();
                    canvas.disposeTimer();
                }
            });

            pack();
            setLocationRelativeTo(null);
            setMinimumSize(new Dimension(980, 720));
        }

        private JPanel buildCenter() {
            JPanel center = new JPanel(new BorderLayout(8, 8));
            JPanel matrixPanel = new JPanel(new BorderLayout(4, 4));
            matrixPanel.setBorder(BorderFactory.createTitledBorder("Adjacency Matrix (custom weights)"));
            matrixPanel.add(new JScrollPane(matrixArea), BorderLayout.CENTER);
            JPanel matrixButtons = new JPanel();
            matrixButtons.add(applyMatrixButton);
            matrixButtons.add(sampleButton);
            matrixPanel.add(matrixButtons, BorderLayout.SOUTH);
            matrixPanel.setPreferredSize(new Dimension(280, 200));
            center.add(matrixPanel, BorderLayout.WEST);
            center.add(canvas, BorderLayout.CENTER);
            return center;
        }

        private JPanel buildControls() {
            JPanel panel = new JPanel(new GridBagLayout());
            panel.setBorder(BorderFactory.createTitledBorder("Simulation Parameters"));
            GridBagConstraints c = new GridBagConstraints();
            c.insets = new Insets(4, 6, 4, 6);
            c.fill = GridBagConstraints.HORIZONTAL;
            c.gridy = 0;

            int col = 0;
            col = addLabeledSpinner(panel, c, col, "Nodes", nodesSpinner);
            col = addLabeledSpinner(panel, c, col, "Workers", threadsSpinner);
            col = addLabeledSpinner(panel, c, col, "Pkt/s", rateSpinner);
            col = addLabeledSpinner(panel, c, col, "Buffer Cap", bufferSpinner);

            c.gridy = 1;
            col = 0;
            col = addLabeledSpinner(panel, c, col, "Congestion Θ", thresholdSpinner);
            col = addLabeledSpinner(panel, c, col, "Cost ×", multiplierSpinner);
            col = addLabeledSpinner(panel, c, col, "Source", sourceSpinner);
            col = addLabeledSpinner(panel, c, col, "Dest", destSpinner);

            c.gridx = col;
            c.weightx = 0;
            panel.add(startButton, c);
            c.gridx = col + 1;
            panel.add(stopButton, c);
            c.gridx = col + 2;
            c.weightx = 1;
            statusLabel.setFont(statusLabel.getFont().deriveFont(Font.BOLD));
            panel.add(statusLabel, c);
            return panel;
        }

        private int addLabeledSpinner(
                JPanel panel,
                GridBagConstraints c,
                int col,
                String label,
                JSpinner spinner
        ) {
            c.gridx = col;
            c.weightx = 0;
            panel.add(new JLabel(label), c);
            c.gridx = col + 1;
            c.weightx = 0.4;
            panel.add(spinner, c);
            return col + 2;
        }

        private JPanel buildScoreboard() {
            JPanel panel = new JPanel(new GridBagLayout());
            panel.setBorder(BorderFactory.createTitledBorder("Live Routing Telemetry"));
            GridBagConstraints c = new GridBagConstraints();
            c.insets = new Insets(6, 10, 6, 10);
            c.gridy = 0;

            int x = 0;
            c.gridx = x++;
            panel.add(metricCaption("Delivered PPS"), c);
            c.gridx = x++;
            panel.add(ppsLabel, c);
            c.gridx = x++;
            panel.add(metricCaption("Delivered"), c);
            c.gridx = x++;
            panel.add(deliveredLabel, c);
            c.gridx = x++;
            panel.add(metricCaption("Dropped"), c);
            c.gridx = x++;
            panel.add(droppedLabel, c);
            c.gridx = x++;
            panel.add(metricCaption("In Flight"), c);
            c.gridx = x++;
            panel.add(inFlightLabel, c);
            c.gridx = x++;
            panel.add(metricCaption("Avg Hops"), c);
            c.gridx = x;
            panel.add(avgHopsLabel, c);
            return panel;
        }

        private static JLabel metricCaption(String text) {
            JLabel label = new JLabel(text);
            label.setForeground(new Color(0x555555));
            return label;
        }

        private static JLabel metricValue(String text) {
            JLabel label = new JLabel(text);
            label.setFont(label.getFont().deriveFont(Font.BOLD, 18f));
            return label;
        }

        private void syncNodeSpinners() {
            int n = ((Number) nodesSpinner.getValue()).intValue();
            sourceSpinner.setModel(new SpinnerNumberModel(
                    Math.min(((Number) sourceSpinner.getValue()).intValue(), n - 1),
                    0,
                    n - 1,
                    1
            ));
            destSpinner.setModel(new SpinnerNumberModel(
                    Math.min(((Number) destSpinner.getValue()).intValue(), n - 1),
                    0,
                    n - 1,
                    1
            ));
        }

        private void loadSampleMesh() {
            int n = ((Number) nodesSpinner.getValue()).intValue();
            double[][] sample = NetworkGraph.sampleMesh(n, System.currentTimeMillis());
            matrixArea.setText(NetworkGraph.formatMatrix(sample));
            applyMatrixPreview();
        }

        private NetworkGraph buildGraphFromUi() {
            double[][] matrix = NetworkGraph.parseMatrix(matrixArea.getText());
            int n = matrix.length;
            nodesSpinner.setValue(n);
            syncNodeSpinners();
            int source = ((Number) sourceSpinner.getValue()).intValue();
            int dest = ((Number) destSpinner.getValue()).intValue();
            if (source >= n) {
                source = 0;
                sourceSpinner.setValue(0);
            }
            if (dest >= n || dest == source) {
                dest = Math.min(n - 1, source + 1);
                destSpinner.setValue(dest);
            }
            return new NetworkGraph(
                    matrix,
                    ((Number) bufferSpinner.getValue()).intValue(),
                    ((Number) thresholdSpinner.getValue()).doubleValue(),
                    ((Number) multiplierSpinner.getValue()).doubleValue()
            );
        }

        private void applyMatrixPreview() {
            try {
                previewGraph = buildGraphFromUi();
                canvas.setGraph(previewGraph);
                statusLabel.setText("Matrix applied (" + previewGraph.size() + " routers)");
            } catch (RuntimeException ex) {
                statusLabel.setText("Matrix error: " + ex.getMessage());
            }
        }

        private SimulationConfig readConfigFromUi(NetworkGraph graph) {
            int n = graph.size();
            int source = ((Number) sourceSpinner.getValue()).intValue();
            int dest = ((Number) destSpinner.getValue()).intValue();
            if (source == dest) {
                throw new IllegalArgumentException("source and destination must differ");
            }
            return new SimulationConfig(
                    n,
                    ((Number) threadsSpinner.getValue()).intValue(),
                    ((Number) rateSpinner.getValue()).intValue(),
                    ((Number) bufferSpinner.getValue()).intValue(),
                    ((Number) thresholdSpinner.getValue()).doubleValue(),
                    ((Number) multiplierSpinner.getValue()).doubleValue(),
                    source,
                    dest,
                    initialConfig.hopMillis()
            );
        }

        private void setControlsEnabled(boolean enabled) {
            nodesSpinner.setEnabled(enabled);
            threadsSpinner.setEnabled(enabled);
            rateSpinner.setEnabled(enabled);
            bufferSpinner.setEnabled(enabled);
            thresholdSpinner.setEnabled(enabled);
            multiplierSpinner.setEnabled(enabled);
            sourceSpinner.setEnabled(enabled);
            destSpinner.setEnabled(enabled);
            matrixArea.setEnabled(enabled);
            applyMatrixButton.setEnabled(enabled);
            sampleButton.setEnabled(enabled);
            startButton.setEnabled(enabled);
            stopButton.setEnabled(!enabled);
        }

        private void startSimulation() {
            if (worker != null && !worker.isDone()) {
                return;
            }
            try {
                NetworkGraph graph = buildGraphFromUi();
                canvas.setGraph(graph);
                SimulationConfig config = readConfigFromUi(graph);
                List<Integer> probe = Pathfinder.shortestPath(graph, config.sourceNode(), config.destinationNode());
                if (probe.isEmpty()) {
                    statusLabel.setText("No path from source to destination");
                    return;
                }
                engine = new RoutingEngine(config, graph);
                setControlsEnabled(false);
                statusLabel.setText("Routing (" + config.workerThreads() + " workers, "
                        + config.packetsPerSecond() + " pkt/s)");
                ppsLabel.setText("0.0");
                deliveredLabel.setText("0");
                droppedLabel.setText("0");
                inFlightLabel.setText("0");
                avgHopsLabel.setText("0.00");

                worker = new SimulationWorker(
                        engine,
                        canvas,
                        ppsLabel,
                        deliveredLabel,
                        droppedLabel,
                        inFlightLabel,
                        avgHopsLabel,
                        statusLabel,
                        () -> setControlsEnabled(true)
                );
                worker.execute();
            } catch (RuntimeException ex) {
                statusLabel.setText("Start error: " + ex.getMessage());
            }
        }

        private void stopSimulation() {
            if (worker != null) {
                worker.requestStop();
            }
            if (engine != null) {
                engine.stop();
            }
        }
    }

    // -------------------------------------------------------------------------
    // CLI parsing + main
    // -------------------------------------------------------------------------

    static SimulationConfig parseArgs(String[] args) {
        int nodes = SimulationConfig.DEFAULTS.nodeCount();
        int threads = SimulationConfig.DEFAULTS.workerThreads();
        int rate = SimulationConfig.DEFAULTS.packetsPerSecond();
        int buffer = SimulationConfig.DEFAULTS.bufferCapacity();
        double threshold = SimulationConfig.DEFAULTS.congestionThreshold();
        double multiplier = SimulationConfig.DEFAULTS.congestionMultiplier();
        int source = SimulationConfig.DEFAULTS.sourceNode();
        int dest = SimulationConfig.DEFAULTS.destinationNode();
        long hopMillis = SimulationConfig.DEFAULTS.hopMillis();

        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            switch (arg) {
                case "--nodes" -> nodes = Integer.parseInt(requireValue(args, ++i, arg));
                case "--threads" -> threads = Integer.parseInt(requireValue(args, ++i, arg));
                case "--rate" -> rate = Integer.parseInt(requireValue(args, ++i, arg));
                case "--buffer" -> buffer = Integer.parseInt(requireValue(args, ++i, arg));
                case "--threshold" -> threshold = Double.parseDouble(requireValue(args, ++i, arg));
                case "--multiplier" -> multiplier = Double.parseDouble(requireValue(args, ++i, arg));
                case "--source" -> source = Integer.parseInt(requireValue(args, ++i, arg));
                case "--dest" -> dest = Integer.parseInt(requireValue(args, ++i, arg));
                case "--hop-ms" -> hopMillis = Long.parseLong(requireValue(args, ++i, arg));
                case "--help", "-h" -> {
                    printUsage();
                    System.exit(0);
                }
                default -> throw new IllegalArgumentException("Unknown argument: " + arg);
            }
        }

        if (source >= nodes) {
            source = 0;
        }
        if (dest >= nodes || dest == source) {
            dest = Math.max(1, nodes / 2);
            if (dest == source) {
                dest = (source + 1) % nodes;
            }
        }

        return new SimulationConfig(
                nodes,
                threads,
                rate,
                buffer,
                threshold,
                multiplier,
                source,
                dest,
                hopMillis
        );
    }

    private static String requireValue(String[] args, int index, String flag) {
        if (index >= args.length) {
            throw new IllegalArgumentException("Missing value for " + flag);
        }
        return args[index];
    }

    private static void printUsage() {
        System.out.println("""
                Usage: java NetworkRoutingSimulator [options]

                  --nodes N           Number of routers / matrix size (default 8)
                  --threads N         Hop worker virtual threads (default 8)
                  --rate N            Packet inject rate per second (default 40)
                  --buffer N          Per-router buffer capacity (default 32)
                  --threshold F       Congestion utilization trigger in (0,1] (default 0.7)
                  --multiplier F      Live cost multiplier when congested (default 4.0)
                  --source I          Source node index (default 0)
                  --dest I            Destination node index (default n/2)
                  --hop-ms MS         Animation duration per hop (default 180)
                  --help              Show this help

                Paste a custom adjacency matrix in the UI before Start. Zero means no link.
                """);
    }

    public static void main(String[] args) {
        final SimulationConfig config;
        try {
            config = parseArgs(args);
        } catch (RuntimeException ex) {
            System.err.println("Configuration error: " + ex.getMessage());
            printUsage();
            System.exit(1);
            return;
        }

        SwingUtilities.invokeLater(() -> {
            try {
                UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
            } catch (Exception ignored) {
                // Fall back to the default cross-platform L&F.
            }
            RoutingFrame frame = new RoutingFrame(config);
            frame.setVisible(true);
        });
    }
}
