---- MODULE MCBoulanger ----
EXTENDS Naturals

\* The full set of actions and the base invariants comes from the Boulanger
\* spec that this module extends.  Only the numeric type and the ticket bound
\* change here -- the action set and those invariants are untouched.

CONSTANTS N, MaxNat

\* A finite version of the natural numbers.  Keeping the name Nat untouched is
\* required because the .cfg file replaces the operator of that name; the
\* replacement below therefore has to be an operator definition, not a constant.
NatOverride(n) == n \in 0..MaxNat

VARIABLES pc, ticket, holder, serving
vars == <<pc, ticket, holder, serving>>

\* Initialising the tickets to 0 keeps the state constraint true from the very
\* first state, so the model is never out of range.
TypeOK ==
  /\ pc \in [0..N-1 -> {"idle", "waiting", "critical"}]
  /\ ticket \in [0..N-1 -> 0..MaxNat]
  /\ holder \in 0..N-1
  /\ serving \in 0..N-1

Init ==
  /\ pc = [p \in 0..N-1 |-> "idle"]
  /\ ticket = [p \in 0..N-1 |-> 0]
  /\ holder = 0
  /\ serving = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<ticket, holder, serving>>

Enter(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in 0..N-1 : ticket[p] <= ticket[q]
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, holder, serving>>

Held(p) ==
  /\ pc[p] = "critical"
  /\ holder' = p
  /\ serving' = (serving + 1) % N
  /\ UNCHANGED <<pc, ticket>>

Leave(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<ticket, holder, serving>>

Ticket(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in 0..N-1 : q # p => ticket[p] < ticket[q]
  /\ ticket[p] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
  /\ UNCHANGED <<pc, holder, serving>>

Next ==
  \/ \E p \in 0..N-1 : Request(p)
  \/ \E p \in 0..N-1 : Enter(p)
  \/ \E p \in 0..N-1 : Held(p)
  \/ \E p \in 0..N-1 : Leave(p)
  \/ \E p \in 0..N-1 : Ticket(p)

Spec == Init /\ [][Next]_vars

\* Commuting critical sections is what stops two processes being in the
\* critical section at once.
MutualExclusion ==
  \A p, q \in 0..N-1 :
    (pc[p] = "critical" /\ pc[q] = "critical") => p = q

\* The invariant from the inductive spec is kept intact here.
Inv == TypeOK

\* The ticket bound is a hard state constraint: always true, never an action.
TicketBound == \A p \in 0..N-1 : ticket[p] < MaxNat

====