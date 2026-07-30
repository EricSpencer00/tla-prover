---- MODULE MCBoulanger ----
EXTENDS Naturals

\* The reference configuration replaces the unbounded Nat operator with a finite
\* version so the model is checkable; the name Nat on the left is therefore
\* never declared here -- only NatOverride is defined.
NatOverride(n) == n

CONSTANTS N, MaxNat

Processes == 1..N

VARIABLES inCS, wants, ticket
vars == <<inCS, wants, ticket>>

TypeOK ==
  /\ inCS \in [Processes -> BOOLEAN]
  /\ wants \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> 0..MaxNat]

Init ==
  /\ inCS = [p \in Processes |-> FALSE]
  /\ wants = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> 0]

Request(p) ==
  /\ ~wants[p]
  /\ ~inCS[p]
  /\ wants' = [wants EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, ticket>>

Enter(p) ==
  /\ wants[p]
  /\ \A q \in Processes : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat THEN ticket[p] + 1 ELSE ticket[p]]
  /\ UNCHANGED wants

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ wants' = [wants EXCEPT ![p] = FALSE]
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in Processes : Request(p)
  \/ \E p \in Processes : Enter(p)
  \/ \E p \in Processes : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in Processes : (inCS[p] /\ inCS[q]) => p = q

Inv ==
  /\ TypeOK
  /\ \A p \in Processes :
       /\ inCS[p] => wants[p]
       /\ inCS[p] => \A q \in Processes : ticket[p] <= ticket[q]
  /\ \A p \in Processes : ticket[p] < MaxNat

====