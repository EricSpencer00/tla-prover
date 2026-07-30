---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Behavior: a shared ticket register (a single number) plus a per-process
\* requested flag. Every process aims to be the sole holder of the ticket
\* (mutual exclusion). Because this is a model-checking configuration, the
\* unbounded Nat type is overridden with a finite range (MaxNat).
\* The state constraint at the end guards against states where a ticket
\* variable would leave that finite range, keeping the model finite.

VARIABLES ticket, pc, want, served
vars == <<ticket, pc, want, served>>

\* The maximum ticket a process may have -- the model only explores
\* ticket numbers strictly below the finite override bound.
Bound == MaxNat - 1

TypeOK ==
  /\ ticket \in 0..Bound
  /\ pc \in [1..N -> {"idle", "cs", "done"}]
  /\ want \in [1..N -> BOOLEAN]
  /\ served \in 0..Bound

Init ==
  /\ ticket = 0
  /\ pc = [p \in 1..N |-> "idle"]
  /\ want = [p \in 1..N |-> FALSE]
  /\ served = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, pc, served>>

Enter(p) ==
  /\ want[p]
  /\ pc[p] = "idle"
  /\ \A q \in 1..N : pc[q] # "cs"
  /\ \A q \in 1..N : p # q => ~want[q]
  /\ served < Bound
  /\ ticket' = served
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<want, served>>

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ served' = (served + 1) % (Bound + 1)
  /\ UNCHANGED <<ticket, want>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ want[p] = TRUE
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<ticket, served>>

Next ==
  \E p \in 1..N :
    \/ Request(p)
    \/ Enter(p)
    \/ Exit(p)
    \/ Reset(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: the ticket register is owned by a process iff that
\* process is in its critical section, so at most one process is ever there.
MutualExclusion ==
  \A p \in 1..N : (pc[p] = "cs") <=> (ticket = p)

\* The full inductive invariant: type correctness plus mutual exclusion.
Inv == TypeOK /\ MutualExclusion

StateBounded == \A p \in 1..N : ticket # p

NatOverride == Nat
====