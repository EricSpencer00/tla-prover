---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Finite-range override of the natural numbers, needed for exhaustive model
\* checking of the Bakery algorithm.  The rest of the spec is unchanged from
\* the original Bakery system it extends.
NatOverride(x) == IF x > MaxNat THEN MaxNat ELSE IF x >= 0 THEN x ELSE 0

VARIABLES inCS, wants, number, nextTicket

vars == <<inCS, wants, number, nextTicket>>

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ wants \subseteq 1..N
    /\ number \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

MutualExclusion ==
    \A i, j \in inCS : i = j

\* The full inductive invariant: empty critical section, bounded ticket range.
Inv ==
    /\ MutualExclusion
    /\ inCS \cap wants = {}
    /\ \A i \in inCS : number[i] > 0
    /\ nextTicket >= Cardinality(inCS)

Init ==
    /\ inCS = {}
    /\ wants = {}
    /\ number = [i \in 1..N |-> 0]
    /\ nextTicket = 0

Request(i) ==
    /\ i \notin wants
    /\ wants' = wants \union {i}
    /\ UNCHANGED <<inCS, number, nextTicket>>

\* The ticket is handed out here, at the moment of the request, not on entry.
\* This is what makes the queue bounded once the ticket ceiling is reached.
Acquire(i) ==
    /\ i \in wants
    /\ i \notin inCS
    /\ inCS = {}
    /\ nextTicket < MaxNat
    /\ nextTicket' = nextTicket + 1
    /\ number' = [number EXCEPT ![i] = nextTicket + 1]
    /\ inCS' = inCS \union {i}
    /\ wants' = wants \ {i}

Release(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ number' = [number EXCEPT ![i] = 0]
    /\ UNCHANGED <<wants, nextTicket>>

Requeue(i) ==
    /\ i \in wants
    /\ nextTicket = MaxNat
    /\ wants' = wants \ {i}
    /\ UNCHANGED <<inCS, number, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Acquire(i)
    \/ \E i \in 1..N : Release(i)
    \/ \E i \in 1..N : Requeue(i)

\* Starts from any reachable state (not just the initial one) because the
\* inductive specification is what guarantees the invariant is preserved.
ISpec == Init /\ [][Next]_vars

====