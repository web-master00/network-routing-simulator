# Network Routing Simulator

A graph simulation of dynamic packet routing. Routers are vertices and links are weighted edges. Shortest paths are recomputed with Dijkstra against a live cost matrix, and congested routers raise the cost of their links so later packets take a less loaded path.

Hop workers share the cost matrix under a read/write lock. Packets move through a `BlockingQueue` on virtual threads, and a Swing canvas draws hops and buffer pressure without blocking the UI thread.

## What it covers

- **Runtime topology.** Node count, packet rate, buffer size, and congestion threshold come from the CLI or Swing controls. No network layout is baked into the binary.
- **Thread-safe Dijkstra.** Paths are recalculated against the current cost matrix so concurrent hop workers do not race.
- **Congestion-aware rerouting.** When a router buffer passes the threshold, incident link costs rise and later packets are steered away.
- **Queued packet stream.** Discrete packets flow through a `BlockingQueue` driven by virtual threads.

Useful as a prototype for SDN controllers, telecom-style path selection, and live congestion drills.

## Requirements

- JDK 21 or newer

## Run

```bash
javac NetworkRoutingSimulator.java
java NetworkRoutingSimulator --nodes 8 --rate 40 --buffer 32 --threshold 0.7
```

Defaults are 8 routers, 8 worker threads, 40 packets per second, a buffer of 32, a congestion threshold of `0.70`, a congestion cost multiplier of `4`, source node `0`, destination node `4`, and a 180 ms hop. At least two nodes are required, and the source and destination must differ.

With no CLI arguments, the program opens a Swing window for node count, rate, buffer size, and congestion threshold.
