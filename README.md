# Golang Kinesis Client Library (gokcl)

A ground up re-write of [Gokini](https://github.com/patrobinson/gokini), based on the [Amazon Kinesis Client Library](https://github.com/awslabs/amazon-kinesis-client).

## Project Goals

This project aims to provide feature parity with the [Kinesis Client Library](https://github.com/awslabs/amazon-kinesis-client) including:

- [] Enumerates shards

- [] Coordinates shard associations with other workers

- [] Instantiates a record processor for every shard it manages

- [] Checkpoints processed records

- [] Balances shard-worker associations when the worker instance count changes

- [] Balances shard-worker associations when shards are split or merged

- [] Instrumentation that supports CloudWatch (partial support)

- [] Support enhanced fan-out consumers

- [] Support aggregated records from Kinesis Producer library
