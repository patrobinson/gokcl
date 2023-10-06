---- MODULE proof ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  Node,
  Shard

VARIABLES Allocation

NoNode == CHOOSE n : n \notin Node
NoShard == CHOOSE n : n \notin Shard
ShardAllocation == [Shard -> Node \union {NoNode}]
vars == << Allocation >>

TypeInvariant ==
  /\ Allocation \in ShardAllocation

Init ==
        /\ Allocation = [ s \in Shard |-> NoNode ]

AllocateFreeShard(w) ==
    LET
        shard == CHOOSE s \in Shard: TRUE
    IN
        IF Allocation[shard] = NoNode
        THEN Allocation' = [Allocation EXCEPT ![shard] = w]
        ELSE UNCHANGED Allocation

Next == 
    \E n \in Node: AllocateFreeShard(n)

Spec == Init /\ [][Next]_vars

====
