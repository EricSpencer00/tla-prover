---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES inCS, ticket, choosing

vars == <<inCS, ticket, choosing>>

TypeOK ==
  /\ inCS \in [0..N]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ choosing \subseteq (1..N)

MutualExclusion ==
  inCS <= 1

\* The bakery's full inductive invariant: request numbers stay within the
\* configured maximum, and only the one current holder is ever in the CS.
Inv ==
  /\ MutualExclusion
  /\ \A i \in 1..N : ticket[i] <= MaxNat
  /\ \A i \in 1..N : i \in choosing

Init ==
  /\ inCS = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ choosing = {}

\* A process takes a request number (ticket) before it may enter the CS.
Request(i) ==
  /\ i \notin choosing
  /\ inCS = 0
  /\ i \notin choosing
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = 1]
  /\ choosing' = choosing \cup {i}
  /\ UNCHANGED inCS

Enter(i) ==
  /\ i \in choosing
  /\ inCS = 0
  /\ inCS' = 1
  /\ UNCHANGED <<ticket, choosing>>

Exit(i) ==
  /\ i \in choosing
  /\ inCS = 1
  /\ inCS' = 0
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ choosing' = choosing \ {i}

Next ==
  \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec

\* The .cfg file substitutes Nat with a finite set derived from MaxNat; the
\* name Nat is retained here so the substitution can target it.
NatOverride == Nat

====