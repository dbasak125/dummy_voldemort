# dummy_voldemort
A Voldemort like distributed Key-Value store with replication and fault-tolerance built in

<p1>Update1: Completed the basic distributed system modeling in TLA+ specification language, for Client-Side routing. I am checking the safety property of the system by defining an Invariant function over the TLA+ specification, and confirming the behaviour with various counts of Read Quorum, Write Quorum and FAILNODES.</p1>

<p2>Update2: Completed the basic distributed system modeling, for Chain-Replication fault tolerance (server-side routing). I am checking the safety property of the system by defining two Invariant function over the TLA+ specification, and confirming single-copy consistency in the db with various node counts, client # and FAILNODES configuration.</p2>
<p3>Will keep this space updated with latest developments regarding the actual implementation code and feature additions.</p3>
