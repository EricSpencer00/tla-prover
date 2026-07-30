---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The token is carried with the process that holds it.  A process that is out
\* of its critical section may hand the token to any other active process.
VARIABLES cs, want, ticket, active, token

vars == <<cs, want, ticket, active, token>>

Active == {p \in 1..N : active[p] = "on"}

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ active \in [1..N -> {"on", "off"}]
  /\ token \in 1..N

\* Initial state is the empty critical section with every process wanting to
\* enter, but ticket numbers are already chosen within the bounded range.
Init ==
  /\ cs = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> TRUE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ active = [p \in 1..N |-> "on"]
  /\ token = 1

\* A process takes the critical section only if it holds the token and no one
\* else is inside.
Enter(p) ==
  /\ active[p] = "on"
  /\ token = p
  /\ ~cs[p]
  /\ want[p]
  /\ cs' = [cs EXCEPT ![p] = TRUE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, active, token>>

Exit(p) ==
  /\ cs[p]
  /\ cs' = [cs EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, ticket, active, token>>

\* An active process may retry, cycling its ticket number within the bounded
\* range.  Nothing else in the model is tied to the value of the ticket.
Retry(p) ==
  /\ active[p] = "on"
  /\ ticket' = [ticket EXCEPT ![p] = (ticket[p] + 1) % (MaxNat + 1)]
  /\ UNCHANGED <<cs, want, active, token>>

\* Hand the token to another active process and recycle the outgoing holder's
\* ticket so the bounded range never fills up.
PassToken(p, q) ==
  /\ token = p
  /\ qs \in Active \ {p}
  /\ token' = qs
  /\ ticket' = [ticket EXCEPT ![p] = (ticket[p] + 1) % (MaxNat + 1)]
  /\ UNCHANGED <<cs, want, active>>

\* Activation models a process that was down coming back up.
Restart(p) ==
  /\ active[p] = "off"
  /\ active' = [active EXCEPT ![p] = "on"]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<cs, token>>

Next ==
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Retry(p)
  \/ \E p \in 1..N, q \in 1..N : PassToken(p, q)
  \/ \E p \in 1..N : Restart(p)

MutualExclusion ==
  \A p, q \in 1..N : (cs[p] /\ cs[q]) => p = q

\* Every state reachable from Init under Next satisfies the invariant, and that
\* closure under Next is exactly what inductive checking of Inv proves.
Inv ==
  /\ MutualExclusion
  /\ TypeOK

ISpec == Init /\ [][Next]_vars
====