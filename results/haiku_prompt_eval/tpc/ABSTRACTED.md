# Intentionally Abstracted Away

This minimal TLA+ model of two-phase commit focuses on safety properties and deliberately abstracts away the following aspects:

## Communication and Networking
- **Message passing delays**: Voting and coordinator decision are instantaneous; no modeling of message transmission time or delivery order.
- **Network partitions**: Assumes full connectivity; no Byzantine failures or partition scenarios modeled.
- **Message acknowledgment protocol**: No explicit message send/receive or acknowledgment tracking.

## Failure Handling and Recovery
- **Timeout logic**: No modeling of timeouts that would trigger retry or failover mechanisms.
- **Crash recovery**: Assumes all participants remain operational; no recovery from coordinator or RM failures.
- **Durability and logging**: No write-to-disk, journals, or durable state transitions. State changes are instantaneous.
- **Transactional undo logs**: No modeling of undo/redo mechanisms or recovery logs.

## Concurrency and Scalability
- **Multiple concurrent transactions**: Models only a single transaction; no interleaving of multiple independent transactions.
- **Lock management**: No modeling of locks, resource allocation, deadlock, or lock timeouts.
- **Resource exhaustion**: No modeling of resource limits or contention.

## Coordinator Architecture
- **Coordinator redundancy**: Single coordinator only; no modeling of backup coordinators or failover.
- **Coordinator group commit protocols**: No Paxos, Raft, or other consensus protocols for coordinator election.

## Data and Semantics
- **Transactional data**: No modeling of what data is being committed or application-level semantics.
- **Database constraints**: No modeling of ACID properties at the data level (only commit/abort outcomes).
- **Isolation levels**: No modeling of transaction isolation or dirty read/phantom scenarios.

## Protocol Optimizations and Variants
- **Precommit phases**: No separate prepare-to-commit or precommit phases beyond the basic vote/decide/execute cycle.
- **Adaptive ordering**: No optimization of RM ordering or batching across transactions.
- **Lazy commit**: No lazy decision-making or deferred commit logic.
- **Async commit**: All decisions and executions are modeled as atomic steps.

## Implementation Details
- **Message payload contents**: No modeling of actual transaction data, RM-specific metadata, or transaction IDs.
- **Data structure implementation**: No modeling of internal queues, state storage, or RM-side persistence.
- **Clock synchronization**: No modeling of wall-clock time, logical timestamps, or clock skew.

These abstractions are justified because the model verifies the fundamental safety property: **atomicity**—ensuring that either all resource managers commit together or all abort together, regardless of the implementation details above.
