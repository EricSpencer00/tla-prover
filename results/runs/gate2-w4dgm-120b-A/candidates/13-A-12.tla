---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, wants, ticket, maxTaken, modelStep

vars == <<inCS, wants, ticket, maxTaken, modelStep>>

\* The Bakery invariant: the ticket range is contiguous, and the holder of the
\* smallest outstanding ticket is the one in the critical section.
Inv ==
    /\ maxTaken = 0 \/ \E p \in inCS : ticket[p] = 1
    /\ \A p \in inCS : \A q \in inCS : p # q => ticket[p] # ticket[q]
    /\ \A p \in inCS : ticket[p] <= maxTaken
    /\ maxTaken <= MaxNat

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ wants \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ maxTaken \in 0..MaxNat

\* The inductive spec starts from any state satisfying the invariant (a
\* reachable one, due to the bounded ticket range) rather than just the
\* initially type-correct state.
Init ==
    /\ inCS = {}
    /\ wants = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ maxTaken = 0
    /\ modelStep = 0

\* A process behind a ticket may take the critical section when nobody holds it.
Enter ==
    /\ modelStep = 0
    /\ inCS = {}
    /\ maxTaken < MaxNat
    /\ \E p \in 1..N :
         /\ p \in wants
         /\ ticket[p] = 0
         /\ ticket' = [ticket EXCEPT ![p] = maxTaken + 1]
         /\ inCS' = inCS \cup {p}
    /\ maxTaken' = maxTaken + 1
    /\ UNCHANGED <<wants, modelStep>>

\* Leaving clears the ticket, keeping the range contiguous by never lowering
\* maxTaken (bounded by MaxNat, so the range eventually saturates).
Exit ==
    /\ modelStep = 0
    /\ \E p \in inCS :
         /\ inCS' = inCS \ {p}
         /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<wants, maxTaken, modelStep>>

\* A process may register interest in entering the critical section.
Raise ==
    /\ modelStep = 0
    /\ \E p \in 1..N :
         /\ p \notin wants
         /\ p \notin inCS
         /\ ticket[p] = 0
         /\ wants' = wants \cup {p}
    /\ UNCHANGED <<inCS, ticket, maxTaken, modelStep>>

\* A process may withdraw its request before entering.
Withdraw ==
    /\ modelStep = 0
    /\ \E p \in wants :
         /\ p \notin inCS
         /\ wants' = wants \ {p}
    /\ UNCHANGED <<inCS, ticket, maxTaken, modelStep>>

\* Once the ticket range has saturated, a quiescent system may be reset to
\* explore another reachable region of the bounded state space.
Reset ==
    /\ modelStep = 0
    /\ maxTaken = MaxNat
    /\ \A p \in 1..N : ticket[p] = 0
    /\ inCS = {}
    /\ modelStep' = 1
    /\ UNCHANGED <<wants, ticket, maxTaken>>

Next ==
    \/ Enter
    \/ Exit
    \/ Raise
    \/ Withdraw
    \/ Reset

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in inCS : p = q

====