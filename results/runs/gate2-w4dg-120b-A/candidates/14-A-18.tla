---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

CONSTANT DefaultMaxNat == 3

RECURSIVE Max(_)
Max(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

\* The Boulangerier algorithm assigns a ticket to any process that has not
\* already been assigned one; the highest existing ticket is the next free
\* number.  Because the model overrides Nat with a finite range, the
\* state-constraint below that prunes away states where a ticket number
\* would reach the bound is essential to keep the reachable state space
\* finite.
Tickets == 0..(MaxNat - 1)

VARIABLES ticket
vars == <<ticket>>

TypeOK ==
  /\ ticket \in [1..N -> Tickets \cup {0}]
  /\ Nat \in Tickets

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ Nat \in Tickets

\* Assigns a new ticket number to any unassigned process, drawn from one
\* above the current maximum.
Assign(i) ==
  /\ ticket[i] = 0
  /\ \A j \in 1..N : ticket[j] # Nat
  /\ Nat < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = Nat]
  /\ Nat' = Nat + 1
  /\ UNCHANGED <<>>

\* Allows the ticket numbers to roll over once the bound is reached, so the
\* model can keep exploring without a hard upper limit on Nat.
Recycle ==
  /\ Nat = MaxNat
  /\ Nat' = 0
  /\ ticket' = [i \in 1..N |-> 0]
  /\ UNCHANGED <<>>

Next ==
  \/ \E i \in 1..N : Assign(i)
  \/ Recycle

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (ticket[i] # 0 /\ ticket[i] = ticket[j]) => i = j

\* The inductive invariant: once a ticket is assigned it is distinct and
\* non-zero, so the critical section is accessed by at most one process.
Inv ==
  /\ \A i, j \in 1..N : (ticket[i] # 0 /\ ticket[i] = ticket[j]) => i = j
  /\ \A i \in 1..N : ticket[i] # 0 => ticket[i] \in Tickets
  /\ Nat \in Tickets

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====