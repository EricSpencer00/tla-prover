---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Finite ticket range: overrides the standard Nat (infinite) to keep the
\* model finite; the .cfg expects this name to replace Naturals' Nat.
NatOverride == 0..MaxNat

\* Mapped-from-Boulanger: administration in a bakery runs with a token
\* ring over N bakers, each holding a ticket number. A baker may enter the
\* proofing stage only while holding the ring token and carrying a
\* ticket strictly below the current ticket ceiling.
Bakers == 0..(N - 1)
Succ(b) == (b + 1) % N
InCS == { b \in Bakers : pc[b] = "cs" }

VARIABLES token, pc, ticket, ceiling
vars == << token, pc, ticket, ceiling >>

TypeOK ==
  /\ token \in Bakers
  /\ pc \in [Bakers -> {"idle", "cs"}]
  /\ ticket \in [Bakers -> NatOverride]
  /\ ceiling \in NatOverride

Init ==
  /\ token = 0
  /\ pc = [b \in Bakers |-> "idle"]
  /\ ticket = [b \in Bakers |-> 0]
  /\ ceiling = 1

\* The ring token advances and brings a fresh ticket ceiling, never
\* lowering the ceiling below a ticket already in flight.
PassToken ==
  /\ token' = Succ(token)
  /\ ceiling' = IF ceiling < MaxNat THEN ceiling + 1 ELSE ceiling
  /\ UNCHANGED << pc, ticket >>

\* The current token holder takes the proofing stage, provided its ticket
\* is still below the ceiling.
Enter(b) ==
  /\ token = b
  /\ pc[b] = "idle"
  /\ ticket[b] < ceiling
  /\ pc' = [pc EXCEPT ![b] = "cs"]
  /\ UNCHANGED << token, ticket, ceiling >>

\* Leaving the stage is a normal unlock: the baker brushes a live ticket
\* to the new ceiling and steps back to idle.
Exit(b) ==
  /\ pc[b] = "cs"
  /\ pc' = [pc EXCEPT ![b] = "idle"]
  /\ ticket' = [ticket EXCEPT ![b] = ceiling]
  /\ UNCHANGED << token, ceiling >>

\* A privileged admin can evict a baker from the stage outright (the
\* privileged admin override), and it does so without touching the ring
\* token, so an evicted baker keeps holding (now stale) ticket numbers.
Evict(b) ==
  /\ pc[b] = "cs"
  /\ pc' = [pc EXCEPT ![b] = "idle"]
  /\ UNCHANGED << token, ticket, ceiling >>

\* Ticket numbers saturate at the ceiling, so a baker whose ceiling has
\* reached MaxNat can still be bumped forward one step at a time without
\* ever leaving NatOverride's finite range.
Tick(b) ==
  /\ pc[b] = "idle"
  /\ ticket[b] < ceiling
  /\ ticket' = [ticket EXCEPT ![b] = ticket[b] + 1]
  /\ UNCHANGED << token, pc, ceiling >>

Next ==
  \/ PassToken
  \/ \E b \in Bakers : Enter(b)
  \/ \E b \in Bakers : Exit(b)
  \/ \E b \in Bakers : Evict(b)
  \/ \E b \in Bakers : Tick(b)

Spec == Init /\ [][Next]_vars

\* Safety: at most one baker is ever in the proofing stage at once.
MutualExclusion == \A b1, b2 \in Bakers : (pc[b1] = "cs" /\ pc[b2] = "cs") => b1 = b2

\* Type correctness: all ticket numbers stay inside the finite, model-
\* checking-friendly range.
TypeOK == TypeOK

\* The full mutual-exclusion inductive invariant for the bakery.
Inv == MutualExclusion /\ TypeOK

\* Bounded model checking: any ticket that ever reaches the ceiling is
\* immediately brushed to it, so no run can drift outside NatOverride.
StateConstraint == \A b \in Bakers : ticket[b] <= ceiling

\* Liveness is not part of this configuration.
====