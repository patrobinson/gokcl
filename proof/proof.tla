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

VARIABLES Allocation, ShardIterator, NodeIterator, SubscriberState, WallClock

\* These are a special kind of value, like NULL
NoNode == CHOOSE n : n \notin Node
NoShard == CHOOSE n : n \notin Shard

InitialIterator == 0

\* These are type definitions, they define all the possible states
\* Nat is the set of all natural numbers (infinite)
Iterator == [Shard -> Nat]
\* Node ∪ {NoNode} produces a set with all nodes and our "Null" value
ShardAllocation == [Shard -> [node: Node \union {NoNode}, lastUpdated: Nat]]
NodeState == [Node -> [ticks: Nat]]

vars == << Allocation, ShardIterator, NodeIterator, SubscriberState, WallClock >>

TypeInvariant ==
  /\ Allocation \in ShardAllocation
  /\ ShardIterator \in Iterator
  /\ NodeIterator \in Iterator
  /\ SubscriberState \in NodeState

\* Returns true if all some shards are not allocated (allocated to NoNode)
UnallocatedShards == {s \in Shard: Allocation[s].node = NoNode}
AllShardsNotAllocated == UnallocatedShards # {}

\* Returns a set of shards allocated to the node that have records to process
NodeShards(n) ==
    {
        s \in Shard:
            (Allocation[s].node = n /\ NodeIterator[s] # ShardIterator[s])
    }

AllocateFreeShard(n) ==
    LET
        shard == CHOOSE s \in UnallocatedShards: TRUE
    IN
        /\ Allocation[shard].node = NoNode
        /\ Allocation' = [Allocation EXCEPT ![shard] = [node |-> n, lastUpdated |-> WallClock]]
        /\ UNCHANGED << NodeIterator, ShardIterator >>



GetRecord(n) ==
    LET
        shard == CHOOSE s \in NodeShards(n): TRUE
    IN
        /\ NodeIterator[shard] # ShardIterator[shard]
        /\ NodeIterator' = [NodeIterator EXCEPT ![shard] = @ + 1]
        /\ Allocation' = [Allocation EXCEPT ![shard].lastUpdated = WallClock]
        /\ UNCHANGED << ShardIterator >>

Subscriber(n) ==
    IF AllShardsNotAllocated
    THEN
        /\ AllocateFreeShard(n)
        /\ SubscriberState' = [SubscriberState EXCEPT ![n].ticks = @ + 1]
    ELSE
        IF ShardIterator = NodeIterator
        THEN 
            /\ TRUE
            /\ UNCHANGED vars
        ELSE
            IF NodeShards(n) = {}
            THEN
                /\ SubscriberState' = [SubscriberState EXCEPT ![n].ticks = @ + 1]
                /\ UNCHANGED << NodeIterator, ShardIterator, Allocation >>
            ELSE
                /\ GetRecord(n)
                /\ SubscriberState' = [SubscriberState EXCEPT ![n].ticks = @ + 1]

DeallocateTimedOutShards == 
    \A s \in Shard: IF WallClock - Allocation[s].lastUpdated > 5
    THEN
        Allocation' = [Allocation EXCEPT ![s].node = NoNode, ![s].lastUpdated = WallClock]
    ELSE
        TRUE


\* Initialise variables
Init ==
        /\ Allocation = [ s \in Shard |-> [node |-> NoNode, lastUpdated |-> 0] ]
        /\ ShardIterator = [ s \in Shard |-> NumberRecordsWritten ]
        /\ NodeIterator = [ s \in Shard |-> InitialIterator ]
        /\ SubscriberState = [ n \in Node |-> [ticks |-> 0] ]
        /\ WallClock = 0

Next == \E n \in Node: Subscriber(n) /\ DeallocateTimedOutShards /\ WallClock' = WallClock + 1

Spec == Init /\ [][Next]_vars

\* Once all publishers and subscribers are finished, all records should be processed
AllRecordsProcessed ==
    <>[](WallClock > 20 => ShardIterator = NodeIterator)

====
