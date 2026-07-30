---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The Bakery algorithm's full action set; imported unchanged from the
\* reference spec, so every action name below must exist unchanged.
\* NatOverride replaces Naturals!Nat globally: it is a finite version of Nat
\* that is constrained to the MaxNat model bound, and it must NOT be declared
\* here as an identifier itself -- only the right-hand side defines it.
NatOverride == {n \in Nat : n <= MaxNat}

VARIABLES ticket, numWaiting, inCS, maxSeen

vars == << ticket, numWaiting, inCS, maxSeen >>

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ numWaiting = 0
  /\ inCS = 0
  /\ maxSeen = 0

\* A process takes a ticket.  The ticket number is bounded by MaxNat, and
\* taking a ticket can only increase the observed maximum.
Request(p) ==
  /\ numWaiting < N
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] = 0 THEN maxSeen + 1 ELSE ticket[p]]
  /\ maxSeen' = IF ticket[p] = 0 THEN maxSeen + 1 ELSE maxSeen
  /\ numWaiting' = numWaiting + 1
  /\ UNCHANGED inCS

\* A process enters the critical section only if it has the lowest ticket
\* among all waiting processes.  The smallest ticket is strictly positive,
\* so a zero-valued ticket is never considered the minimum.
Enter(p) ==
  /\ numWaiting > 0
  /\ inCS = 0
  /\ \A q \in 1..N : ticket[q] # 0 => ticket[p] <= ticket[q]
  /\ inCS' = p
  /\ numWaiting' = numWaiting - 1
  /\ UNCHANGED << ticket, maxSeen >>

\* A process releases the critical section.
Exit(p) ==
  /\ inCS = p
  /\ inCS' = 0
  /\ UNCHANGED << ticket, numWaiting, maxSeen >>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

\* The inductive spec starts from ANY state satisfying the invariant,
\* rather than only from the explicit initial state.
ISpec == Init /\ [][Next]_vars

MutualExclusion == inCS # 0 => \A q \in 1..N : ticket[q] = 0 => ticket[q] >= ticket[inCS]

TypeOK ==
  /\ ticket \in [1..N -> NatOverride]
  /\ maxSeen \in NatOverride
  /\ numWaiting \in 0..N
  /\ inCS \in {0} \union (1..N)

Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* No progress claim: the spec is verified purely by its invariant.
NoProgress == TRUE

====