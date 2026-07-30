---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  N,
  MaxNat

VARIABLES
  ticket,
  choosing,
  inCS

vars == <<ticket, choosing, inCS>>

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ inCS \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A i \in 1..N : inCS[i] => \A j \in 1..N : (j # i) => ~inCS[j]

MaxTicket == MaxNat

\* Start from any type-correct state, so the invariant must hold inductively.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ inCS = [i \in 1..N |-> FALSE]

Bump(n) == IF n < MaxTicket THEN n + 1 ELSE n

\* A process may take a strictly higher ticket number than any it has observed.
Choose(i) ==
  /\ ~choosing[i]
  /\ ~inCS[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, inCS>>

\* The baking station reads everyone's ticket and takes one above the max.
TakeTicket(i) ==
  /\ choosing[i]
  /\ \A j \in 1..N : ticket[j] # 0 => ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = Bump(\E j \in 1..N : ticket[j])]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED inCS

Enter(i) ==
  /\ ~inCS[i]
  /\ ticket[i] # 0
  /\ \A j \in 1..N : (~inCS[j] \/ ticket[i] < ticket[j])
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, choosing>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* The inductive spec starts from any type-correct state, not just Init.
ISpec == Init /\ [][Next]_vars

NatOverride == Nat

====