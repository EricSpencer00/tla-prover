# Intentionally Abstracted Away

This minimal specification focuses exclusively on the safety-relevant state for quorum-based leader election. The following aspects are intentionally omitted:

## Network and Communication
- **Message passing details**: We do not model RPC calls, message delays, or delivery guarantees. Voting is instantaneous and atomic.
- **Message loss and duplication**: We assume all votes are reliably recorded.
- **Network partitions**: We do not model nodes being partitioned from each other.

## Timing and Timeouts
- **Election timeouts**: We do not model the timeout mechanism that triggers term advances; term advances happen non-deterministically in the specification.
- **Heartbeat messages**: We do not model leader heartbeats or follower liveness detection.
- **Real-time constraints**: The specification is untimed; we only care about logical ordering.

## Implementation Details
- **Persistent storage**: We do not model disk writes for durability of terms and votes, though the spec assumes votes persist within a term.
- **Node states (Follower/Candidate/Leader)**: We do not explicitly track node roles; nodes vote and advance terms without explicit state machines.
- **Request handling**: We do not model how a leader handles client requests or applies log entries.
- **Snapshot and log compaction**: Not relevant to the voting protocol itself.

## Election Mechanics
- **Candidate self-votes**: The spec allows any node to receive votes from any node, including not requiring a candidate to vote for itself.
- **Multiple election rounds per term**: We abstract term advances as atomic; re-elections within a term are not modeled.
- **Tie-breaking**: The spec does not model how to handle ties when multiple candidates are seeking votes in the same term (quorum requirement prevents simultaneous majorities, but does not prevent each node from voting for different candidates).

## Failure Scenarios
- **Crash and recovery**: All nodes are assumed to be always up and responsive.
- **Byzantine failures**: We assume nodes are non-Byzantine; they do not lie about their terms or votes.
- **Slow nodes**: All nodes process actions at the same logical rate in the spec.

## Liveness Properties
- **Leader election completeness**: We do not guarantee that an election will eventually complete; the spec is safety-only.
- **Election fairness**: We do not model fairness constraints on who wins elections.

## State Not Modeled
- **Which node initiated an election**: Elections happen spontaneously; we do not track motivation.
- **Node identifiers for votes**: We assume nodes can refer to any node by name; no discovery mechanism is needed.
- **Term boundaries and log synchronization**: We model terms but not the log replication that would accompany them in a real protocol like Raft.

These abstractions make the specification concise and focused on the core safety property: **at most one leader per term, elected by quorum vote**.
