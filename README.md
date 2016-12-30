# dummy_voldemort
A Voldemort like distributed Key-Value store with replication and fault-tolerance built in

Project Description:
Formal specification and implementation of a high-throughput, fail-stop fault-tolerant, Voldemort like distributed datastore.
- Modeling and verification of Chain Replication algorithm in TLA+ 
- Modeling of PAXOS based configurator module (to maintain Head, Tail and chain memberships)
- Implementation in Java using
-> 7 identical centos VMs as replicated storage nodes
-> 1 PAXOS based chain configuration module acting as Master (5 centos VMs, 2-node fail tolerant)
-> Web based Clients (multiple independent)
-> Simulation of various CAP contention scenarios by automating pseudo-random node failures and network partitioning using vmrun scripts on VMware Workstation 12. 


<p1>Update1: Completed the basic distributed system modeling in TLA+ specification language, for Client-Side routing. I am checking the safety property of the system by defining an Invariant function over the TLA+ specification, and confirming the behaviour with various counts of Read Quorum, Write Quorum and FAILNODES.</p1>

<p2>Update2: Completed the basic distributed system modeling, for Chain-Replication fault tolerance (server-side routing). I am checking the safety property of the system by defining two Invariant function over the TLA+ specification, and confirming single-copy consistency in the db with various node counts, client # and FAILNODES configuration.</p2>
<p3>Will keep this space updated with latest developments regarding the actual implementation code and feature additions.</p3>
