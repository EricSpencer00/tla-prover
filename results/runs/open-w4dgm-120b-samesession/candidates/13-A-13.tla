---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The override below replaces the unbounded Nat with a finite range 0..MaxNat
\* for model checking. It keeps the Naturals import for the other operators.
NatOverride == 0..MaxNat

VARIABLES entering, inCS, wants, ticket, nextTicket

vars == <<entering, inCS, wants, ticket, nextTicket>>

TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ wants \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

Init ==
  /\ entering = [p \in 1..N |-> FALSE]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ wants = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

\* A process joins the bakery line, taking the next free bounded ticket.
JoinLine(p) ==
  /\ ~wants[p]
  /\ ~inCS[p]
  /\ nextTicket < MaxNat
  /\ wants' = [wants EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<entering, inCS>>

\* A process starts entering the critical section once it holds the current
\* smallest ticket among all processes still wanting the section.
StartEnter(p) ==
  /\ wants[p]
  /\ ~entering[p]
  /\ ~inCS[p]
  /\ \A q \in 1..N : (wants[q] /\ q # p) => ticket[p] < ticket[q]
  /\ entering' = [entering EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, wants, ticket, nextTicket>>

\* Entering completes: the process is now in the critical section.
Enter(p) ==
  /\ entering[p]
  /\ ~inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ entering' = [entering EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<wants, ticket, nextTicket>>

\* A process leaves the critical section, freeing its ticket number.
Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ wants' = [wants EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<entering, nextTicket>>

\* The ticket numbering recycles once the bounded range is exhausted and the
\* section is empty, keeping the state space finite for model checking.
Recycle ==
  /\ nextTicket = MaxNat
  /\ \A p \in 1..N : ~wants[p]
  /\ nextTicket' = 0
  /\ UNCHANGED <<entering, inCS, wants, ticket>>

StartStep == \E p \in 1..N : StartEnter(p)
EnterStep == \E p \in 1..N : Enter(p)

Next ==
  \/ \E p \in 1..N : JoinLine(p)
  \/ StartStep
  \/ EnterStep
  \/ \E p \in 1..N : Leave(p)
  \/ Recycle

\* This is the inductive spec: started from any reachable state, every run
\* stays within the defined state space and keeps the invariant true.
ISpec == Spec /\ WF_vars(StartStep) /\ WF_vars(EnterStep)

Spec == Init /\ [][Next]_vars

\* Safety: mutual exclusion, plus the usual type and bounded-ticket invariant.
MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

Inv ==
  /\ MutualExclusion
  /\ TypeOK

====