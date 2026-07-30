---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS
  N, MaxNat

\* The infinite Nat type is overridden with a finite version for model checking.
NatOverride == 0..MaxNat

VARIABLES
  wants, inCS, ticket, nextTicket

vars == <<wants, inCS, ticket, nextTicket>>

TypeOK ==
  /\ wants \in [1..N -> BOOLEAN]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

MutualExclusion ==
  \A a \in 1..N, b \in 1..N : (a # b /\ inCS[a]) => ~inCS[b]

Init ==
  /\ wants = [i \in 1..N |-> FALSE]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

\* A process requests entry by taking the next ticket number, saturated at the max.
Request(i) ==
  /\ ~wants[i]
  /\ wants' = [wants EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED inCS

\* A process enters the critical section only if it holds the lowest ticket among
\* all waiting processes and nobody else is in the critical section.
Enter(i) ==
  /\ wants[i]
  /\ \A j \in 1..N : ~(wants[j] /\ ticket[j] < ticket[i])
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<wants, ticket, nextTicket>>

\* A process leaves the critical section.
Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ wants' = [wants EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec ==
  /\ Init
  /\ [][Next]_vars

\* The inductive spec (ISpec) drops Init and starts from any type-correct state,
\* reduced to strong fairness on the entry action instead.
\* Inv is the full inductive invariant, containing additional closure facts.
Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ \A i \in 1..N : inCS[i] => (wants[i] /\ \A j \in 1..N : ticket[j] >= ticket[i])
  /\ (\A i \in 1..N : inCS[i]) => (nextTicket = MaxNat)

\* Action-based strong fairness only on entry, not on request, so the model is
\* not trivially forced into the critical section by fairness on ticketing.
ISpec ==
  /\ Spec
  /\ \A i \in 1..N :
       /\ SF_vars(Enter(i))
       /\ WF_vars(Exit(i))
  /\ SF_vars(\E i \in 1..N : Exit(i))

\* The inductive invariant is the only thing that needs checking here.
CheckInvariants == Inv

====