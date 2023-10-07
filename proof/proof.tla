---- MODULE proof ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS
  Node,
  Shard,
  NumberRecordsWritten

\* These assumptions ensure the constants are valid
\* We must have some nodes and some shards and we must write some records to the shards
ASSUME
    /\ Node # {}
    /\ Shard # {}
    /\ NumberRecordsWritten > 0

VARIABLES Allocation, ShardIterator, NodeIterator

\* These are a special kind of value, like NULL
NoNode == CHOOSE n : n \notin Node
NoShard == CHOOSE n : n \notin Shard

InitialIterator == 0

\* These are type definitions, they define all the possible states
\* Nat is the set of all natural numbers (infinite)
Iterator == [Shard -> Nat]
\* Node ∪ {NoNode} produces a set with all nodes and our "Null" value
ShardAllocation == [Shard -> Node \union {NoNode}]

vars == << Allocation, ShardIterator, NodeIterator >>

TypeInvariant ==
  /\ Allocation \in ShardAllocation
  /\ ShardIterator \in Iterator
  /\ NodeIterator \in Iterator

\* Returns true if all some shards are not allocated (allocated to NoNode)
AllShardsNotAllocated == Allocation \notin [Shard -> Node]

\* Returns a set of shards allocated to the node that have records to process
NodeShards(n) ==
    {
        s \in Shard:
            (Allocation[s] = n /\ NodeIterator[s] # ShardIterator[s])
    }

AllocateFreeShard(w) ==
    LET
        shard == CHOOSE s \in Shard: TRUE
    IN
        /\ AllShardsNotAllocated
        /\ IF Allocation[shard] = NoNode
            THEN Allocation' = [Allocation EXCEPT ![shard] = w]
            ELSE UNCHANGED << Allocation >>
        /\  UNCHANGED << NodeIterator, ShardIterator >>

PutRecord(s) ==
    /\ ShardIterator[s] < NumberRecordsWritten
    /\ ShardIterator' = [ShardIterator EXCEPT ![s] = @ + 1]
    /\ UNCHANGED << NodeIterator, Allocation >>

GetRecord(n) ==
    LET
        shard == CHOOSE s \in NodeShards(n): TRUE
    IN
        /\ NodeIterator[shard] # ShardIterator[shard]
        /\ NodeIterator' = [NodeIterator EXCEPT ![shard] = @ + 1]
        /\ UNCHANGED << ShardIterator, Allocation >>

Subscriber(n) ==
    \/
        /\ AllShardsNotAllocated
        /\ AllocateFreeShard(n)
    \/
        /\ ShardIterator # NodeIterator
        /\ NodeShards(n) # {} /\ GetRecord(n)

Publisher == \E s \in Shard: PutRecord(s)

\* Initialise variables
Init ==
        /\ Allocation = [ s \in Shard |-> NoNode ]
        /\ ShardIterator = [ s \in Shard |-> InitialIterator ]
        /\ NodeIterator = [ s \in Shard |-> InitialIterator ]

\* Publish and process records
\* We use one publisher but n nodes
Next == (\E n \in Node: Subscriber(n))
    \/ Publisher

Spec == Init /\ [][Next]_vars

Allocated == \A s \in Shard: []<>(<<Allocation[s] # NoNode>>_vars)

====
