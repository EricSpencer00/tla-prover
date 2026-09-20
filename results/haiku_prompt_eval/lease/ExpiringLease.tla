---------------------------- MODULE ExpiringLease ----------------------------
(*
Minimal TLA+ model of a distributed lock with expiring leases.

A single grantor issues time-limited leases to multiple clients. A lease is
valid only while current_time < expiry_time. This model ensures:

  - No use-after-expiry: clients cannot use leases after they expire
  - Mutual exclusion: at most one client holds a lease at any time
  - Automatic revocation: expired leases are revoked when time advances

The model is intentionally abstract, omitting network delays, lease renewal,
distributed consensus, and other implementation details (see ABSTRACTED.md).
*)

EXTENDS Naturals

CONSTANTS
  Clients,           (* Set of client identifiers *)
  MaxTime,           (* Upper bound on logical time (for model checking) *)
  LeaseDuration      (* Duration of each issued lease *)

VARIABLES
  currentTime,       (* Current logical time *)
  lockHolder,        (* Client holding lease, or "none" *)
  leaseExpiry        (* Time when current lease expires *)

TypeOK ==
  /\ currentTime \in 0..MaxTime
  /\ lockHolder \in Clients \cup {"none"}
  /\ leaseExpiry \in 0..(MaxTime + LeaseDuration)

Init ==
  /\ currentTime = 0
  /\ lockHolder = "none"
  /\ leaseExpiry = 0

(*
Grantor grants a new lease to a requesting client.
Precondition: the lock is currently free (no one holds it).
Effect: client becomes the holder, lease expires at currentTime + LeaseDuration.
*)
GrantLeaseToClient(client) ==
  /\ lockHolder = "none"
  /\ lockHolder' = client
  /\ leaseExpiry' = currentTime + LeaseDuration
  /\ currentTime' = currentTime

(*
Client releases their held lease.
Precondition: client is the current holder.
Effect: lock becomes free for the next client.
*)
ClientReleasesLease(client) ==
  /\ lockHolder = client
  /\ lockHolder' = "none"
  /\ currentTime' = currentTime
  /\ leaseExpiry' = leaseExpiry

(*
Logical time advances by one unit.
If the current lease has expired (currentTime >= leaseExpiry),
the lease is automatically revoked (holder is cleared).
*)
AdvanceTime ==
  /\ currentTime' = currentTime + 1
  /\ IF currentTime' >= leaseExpiry
     THEN lockHolder' = "none"
     ELSE lockHolder' = lockHolder
  /\ leaseExpiry' = leaseExpiry

Next ==
  \/ \E c \in Clients : GrantLeaseToClient(c)
  \/ \E c \in Clients : ClientReleasesLease(c)
  \/ AdvanceTime

Spec == Init /\ [][Next]_<<currentTime, lockHolder, leaseExpiry>>

(*
INVARIANT: If a client holds the lease, it has not yet expired.
This is the core safety property: no client can use an expired lease.
*)
HeldLeaseIsValid ==
  lockHolder \in Clients => currentTime < leaseExpiry

(*
INVARIANT: Once a lease expires, it is immediately revoked.
The lock cannot be held after currentTime >= leaseExpiry.
*)
ExpiredLeaseIsRevoked ==
  currentTime >= leaseExpiry => lockHolder = "none"

(*
INVARIANT: Mutual exclusion.
At most one client can hold the lease at any time.
This is enforced by requiring the lock to be free before granting a new lease.
*)
MutualExclusion ==
  \A c1, c2 \in Clients :
    (lockHolder = c1 /\ lockHolder = c2) => c1 = c2

=============================================================================
