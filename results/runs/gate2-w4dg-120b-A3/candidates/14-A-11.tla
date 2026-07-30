---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, ticket, served

vars == <<pc, ticket, served>>

\* NatOverride replaces the true Nat from Naturals with a finite version for
\* model checking. It must NOT be declared; it redefines the meaning of Nat.
NatOverride(n) == n % (MaxNat + 1)

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ served = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "wait"]
  /\ ticket' = [ticket EXCEPT ![p] = NatOverride(ticket[p] + 1)]
  /\ UNCHANGED served

Enter(p) ==
  /\ pc[p] = "wait"
  /\ \A q \in 1..N : ~(pc[q] = "cs" /\ ticket[q] < ticket[p])
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<ticket, served>>

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ served' = (served + 1) % (MaxNat + 1)
  /\ UNCHANGED ticket

Requeue(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ served' = (served + 1) % (MaxNat + 1)
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Requeue(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (pc[p] = "cs" /\ pc[q] = "cs") => (p = q)

TypeOK ==
  /\ pc \in [1..N -> {"idle", "wait", "cs", "done"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ served \in 0..MaxNat

\* The full inductive invariant used by the original Boulanger proof.
Inv == MutualExclusion /\ TypeOK

StateBound ==
  \A p \in 1..N : ticket[p] < MaxNat

====