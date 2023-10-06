# GoKCL Proof

[Gokini](https://github.com/patrobinson/gokini) is a Golang port of the [Amazon Kinesis Client Library for Java](https://github.com/awslabs/amazon-kinesis-client) (KCL).
It has had some small success (such as being forked by [VMware](https://github.com/vmware/vmware-go-kcl) and a stream processing tool [Benthos](https://github.com/benthosdev/benthos/commit/df28a6e300067df361cfd52fc128b8ce4619ad00)). But it suffered many challenges with distributed system bugs.

The algorithm was losely based on the KCL implementation, which uses DynamoDB to co-ordinate multiple nodes in effectively balancing Kinesis Shards. The benefit is the nodes automatically discover shards, making them stateless (assuming at-least once processing semantics) and therefore able to self heal and rebalance when shards or nodes are added or deleted.
But this creates challenges and opportunities for bugs.

## Invariants

* Assumption: Eventually nodes start and stay up long enough to process all shard records
* Safety invariant: A node should not write a checkpoint that is less than the current checkpoint
* Safety invariant: A node should never skip processing a record
* Temporal invariant: Each record is eventually processed at least once
* Temporal invariant: Nodes will eventually balance shard allocation fairly

## Failure Model

We want our system to gracefully handle the following failure modes:

* Nodes permenantly or temporarily failing
* Nodes pausing and resuming computation (network partitioning or system lock up)
