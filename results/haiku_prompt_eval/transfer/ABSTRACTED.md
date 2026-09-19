# Intentionally Abstracted Away from LedgerTransfer Model

## Implementation and Infrastructure
- **Transaction IDs**: No transaction sequence numbers or unique identifiers
- **Timestamps**: No temporal ordering or time-based constraints
- **Message Queues**: No request or response buffers; transfers happen instantaneously
- **Persistence**: No durable storage, logs, or recovery mechanisms
- **Consensus Mechanisms**: No Byzantine agreement, Paxos, Raft, or other consensus protocol

## Operational Details
- **Transaction History**: No audit trail or ledger log of past transfers
- **Account Lifecycle**: No account creation, closure, or deletion events
- **Access Control**: No permissions, authentication, or authorization checks
- **Concurrency Control**: No explicit locks, latches, or mutual exclusion (atomicity is assumed at the action level)
- **Failure Modes**: No network delays, timeouts, packet loss, or Byzantine failures
- **Replication**: No multi-ledger copies, synchronization, or consistency protocols

## System Dynamics
- **Fee Mechanisms**: No transaction fees or interest rates
- **Multiple Ledgers**: Only a single ledger; no cross-ledger transfers or currency conversion
- **Partial Transfers**: No notion of transfer rejection after initiation; either the transfer happens or it doesn't
- **Priority Queuing**: No priority levels or fairness constraints on transfer ordering
- **Transfer Cancellation**: No ability to cancel or reverse transfers once initiated

## State and Granularity
- **Balance History**: Only current balances matter; historical snapshots are not tracked
- **In-Flight Transfers**: No representation of partially completed or pending transfers
- **Transfer Metadata**: No tracking of purpose, counterparty information, or memo fields
- **Atomicity Levels**: Transfers are atomic at the ledger level; we do not model sub-operations

## Why These Abstractions Are Valid
The two safety properties—**no negative balances** and **money conservation**—depend only on:
1. The current account balances (what we model)
2. The atomic movement of money between accounts (what we enforce via action guards)

All abstracted details are implementation concerns that do not affect whether these two properties hold. A real ledger system would include these features for robustness, auditability, and operational requirements, but they are orthogonal to the core safety invariants verified by this specification.
