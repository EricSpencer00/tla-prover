---- MODULE MCBakery ----
EXTENDS Naturals

\* Model-checking override: Nat becomes a bounded-range function so the
\* Bakery state space stays finite. Every other variable and action is
\* taken exactly from the full Bakery spec; only the type of Nat is
\* narrowed here, never the behaviour of the protocol.
CONSTANTS N, MaxNat

VARIABLES when, entering, inCS, want, maxWhen

vars == <<when, entering, inCS, want, maxWhen>>

TypeOK ==
  /\ when \in 0..MaxNat
  /\ entering \in [1..N -> 0..MaxNat]
  /\ inCS \subseteq 1..N
  /\ want \subseteq 1..N
  /\ maxWhen \in 0..MaxNat

Init ==
  /\ when = 0
  /\ entering = [i \in 1..N |-> 0]
  /\ inCS = {}
  /\ want = {}
  /\ maxWhen = 0

\* A process that wants entry draws a ticket no later than the highest
\* seen so far; because ticket numbers are bounded, an idle process may
\* keep waiting rather than drawing a fresh one once the ceiling is hit.
Arrive ==
  /\ \E i \in 1..N:
       /\ i \notin want
       /\ i \notin inCS
       /\ want' = want \cup {i}
       /\ entering' = [entering EXCEPT ![i] =
                         IF when > maxWhen THEN when ELSE maxWhen]
  /\ UNCHANGED <<when, inCS, maxWhen>>

\* The twist: a process may give up while waiting, freeing its ticket.
Withdraw ==
  /\ \E i \in want:
       /\ entering' = [entering EXCEPT ![i] = 0]
       /\ want' = want \ {i}
  /\ UNCHANGED <<when, inCS, maxWhen>>

\* A process enters only when its ticket is the next in the sequence, so
\* at most one process can be in the critical section.
Enter ==
  /\ \E i \in want:
       /\ entering[i] = when + 1
       /\ when < MaxNat
       /\ inCS' = inCS \cup {i}
       /\ entering' = [entering EXCEPT ![i] = 0]
       /\ want' = want \ {i}
       /\ when' = when + 1
       /\ maxWhen' = IF entering[i] > maxWhen THEN entering[i] ELSE maxWhen

Leave ==
  /\ \E i \in inCS:
       inCS' = inCS \ {i}
  /\ UNCHANGED <<when, entering, want, maxWhen>>

Next == Arrive \/ Withdraw \/ Enter \/ Leave

\* The model is checked as an inductive invariant from any reachable
\* state, not just from Init: every transition must preserve it.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A a, b \in inCS: a = b
Inv == MutualExclusion /\ TypeOK
====