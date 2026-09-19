# Intentionally Abstracted Away

This TLA+ model captures only the safety-relevant aspects of expiring leases.
The following implementation details are deliberately abstracted:

## Communication & Network

- **Network Delays**: Assumes synchronous, reliable message delivery. Real systems experience latency and potential message loss.
- **Retries & Timeouts**: No modeling of request retries or client-side timeouts when waiting for a lease grant.
- **Message Ordering**: Assumes all messages are processed in order without reordering or duplication.

## Lease Lifecycle

- **Lease Renewal**: Clients cannot renew an active lease before expiry. Real systems allow early renewal to extend holding time.
- **Grantor-Initiated Revocation**: Leases are revoked only via automatic time-based expiration, not by explicit grantor action (e.g., if a misbehaving client is detected).
- **Lease Tokens & Signatures**: No cryptographic tokens or signatures; leases are abstract (holder identity + expiry time).

## Client Behavior & State

- **Client-Side Lease Cache**: No local caching of lease state; clients always trust the grantor's current assertion.
- **Client Verification**: Clients cannot verify lease authenticity; they implicitly trust the grantor.
- **Fault & Byzantine Behavior**: No faulty or malicious clients/grantors; all follow the specification exactly.

## System Architecture

- **Single Grantor**: Exactly one grantor issues leases. Production systems may use multiple grantors with distributed consensus or primary-backup replication.
- **No Concurrent Grantors**: No modeling of coordination between multiple lease issuers.
- **No Queuing or Fairness**: The model does not represent a queue of waiting clients. Any client can acquire the next available lease non-deterministically.
- **Protected Resource Abstraction**: The actual resource being protected is not modeled; only lease ownership is tracked.

## Temporal & Verification Aspects

- **Logical vs. Wall-Clock Time**: Time is a simple logical counter, not wall-clock time. Real systems deal with clock skew and unsynchronized clocks.
- **Liveness Properties**: The spec focuses on safety. Liveness properties (e.g., "every requesting client eventually acquires a lease") are not verified.
- **Fairness Assumptions**: No fairness constraints; client scheduling is nondeterministic.
- **Clock Monotonicity**: Assumes time never decreases; no modeling of backward time jumps or clock adjustments.

## Other Abstractions

- **Persistence**: No modeling of durable storage; the grantor's state is assumed not to be lost.
- **Partial Synchrony**: Assumes synchronous execution; real systems may experience partial or temporary asynchrony.
- **Scalability**: Model checking is feasible only for small numbers of clients; real systems scale to thousands.
