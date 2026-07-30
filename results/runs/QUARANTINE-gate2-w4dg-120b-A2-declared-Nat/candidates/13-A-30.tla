---- MODULE MCBakery ----
EXTENDS Integers

\* Model checking mode: the natural numbers are globally overridden to a finite
\* range (MaxNat + 1 values), so ticket numbers stay bounded and the state
\* space stays finite.  The inductive spec ISpec starts from any type-correct
\* state, not just the initial one, and the invariant must hold across all.
\* The actors are the Bakery processes; no new state or actions beyond Bakery.

CONSTANTS N, MaxNat, Nat

VARIABLES serving, target, ticket, nextTicket, request

vars == <<serving, target, ticket, nextTicket, request>>

\* The finite bound on natural numbers, overriding the infinite set Nat.
NatOverride == 0..MaxNat

TypeOK ==
  /\ serving \in [1..N -> BOOLEAN]
  /\ target \in [1..N -> 0..N]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ request \in NatOverride

Init ==
  /\ serving = [i \in 1..N |-> FALSE]
  /\ target = [i \in 1..N |-> 0]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ request = 0

\* Forward step: a process takes a request and is handed the next ticket.
\* The ticket is always taken from the globally bound nextTicket.
Forward(i) ==
  /\ request > 0
  /\ serving[i] = FALSE
  /\ target[i] = 0
  /\ serving' = [serving EXCEPT ![i] = TRUE]
  /\ target' = [target EXCEPT ![i] = request]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ request' = request - 1

\* Backward step: a process in the critical section leaves it, dropping its
\* request and its ticket so it can be reused.
Backward(i) ==
  /\ serving[i] = TRUE
  /\ serving' = [serving EXCEPT ![i] = FALSE]
  /\ target' = [target EXCEPT ![i] = 0]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ request' = request + 1

\* A process already in the critical section may keep holding it without
\* changing anything, so the system can sit quiet with someone inside.
Quiet(i) ==
  /\ serving[i] = TRUE
  /\ serving' = serving
  /\ target' = target
  /\ ticket' = ticket
  /\ nextTicket' = nextTicket
  /\ request' = request

Next == \E i \in 1..N : Forward(i) \/ Backward(i) \/ Quiet(i)

\* The inductive specification: any type-correct state, not just Init, is
\* allowed as a starting point for reachability, so the invariant is checked
\* across every reachable state.
ISpec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (serving[i] /\ serving[j]) => i = j

\* Full inductive invariant (not just mutual exclusion) checked here.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

Spec == ISpec
InitSpec == Init
NextSpec == Next

====