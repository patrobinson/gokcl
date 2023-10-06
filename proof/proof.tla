---- MODULE proof ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  Node,
  Shard,
  NumberRecordsWritten

VARIABLES Allocation, ShardIterator, NodeIterator

NoNode == CHOOSE n : n \notin Node
NoShard == CHOOSE n : n \notin Shard
InitialIterator == 0
Iterator == [Shard -> Nat]
ShardAllocation == [Shard -> Node \union {NoNode}]
vars == << Allocation, ShardIterator, NodeIterator >>

TypeInvariant ==
  /\ Allocation \in ShardAllocation
  /\ ShardIterator \in Iterator
  /\ NodeIterator \in Iterator

Init ==
        /\ Allocation = [ s \in Shard |-> NoNode ]
        /\ ShardIterator = [ s \in Shard |-> InitialIterator ]
        /\ NodeIterator = [ s \in Shard |-> InitialIterator ]

AllocateFreeShard(w) ==
    LET
        shard == CHOOSE s \in Shard: TRUE
    IN
        /\ IF Allocation[shard] = NoNode
            THEN Allocation' = [Allocation EXCEPT ![shard] = w]
            ELSE UNCHANGED << Allocation >>
        /\  UNCHANGED << NodeIterator, ShardIterator >>

PutRecord(s) ==
    /\ ShardIterator[s] < NumberRecordsWritten
    /\ ShardIterator' = [ShardIterator EXCEPT ![s] = @ + 1]
    /\ UNCHANGED << NodeIterator, Allocation >>

Subscriber(n) == AllocateFreeShard(n)

Publisher == \E s \in Shard: PutRecord(s)

Next == (\E n \in Node: Subscriber(n))
    \/ Publisher

Spec == Init /\ [][Next]_vars

====
