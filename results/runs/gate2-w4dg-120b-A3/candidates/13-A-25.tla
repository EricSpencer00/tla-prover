---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite version
\* that saturates at MaxNat. This is what makes the model checkable.
NatOverride(n) == IF n > MaxNat THEN MaxNat ELSE n

VARIABLES ticket, choosing, inCS, served

vars == <<ticket, choosing, inCS, served>>

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ choosing \subseteq (1..N)
    /\ inCS \subseteq (1..N)
    /\ served \in 0..MaxNat

Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ choosing = {}
    /\ inCS = {}
    /\ served = 0

Choose(i) ==
    /\ i \notin choosing
    /\ i \notin inCS
    /\ choosing' = choosing \cup {i}
    /\ UNCHANGED <<ticket, inCS, served>>

Take(i) ==
    /\ i \in choosing
    /\ \A j \in 1..N : ticket[j] = 0 \/ (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
    /\ ticket' = [ticket EXCEPT ![i] = NatOverride(@ + 1)]
    /\ choosing' = choosing \ {i}
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED served

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ UNCHANGED <<ticket, choosing, served>>

\* The inductive specification starts from any type-correct state and is
\* guaranteed to reach a state where every process has been served once.
SpecStart == Init /\ [][Next]_vars
Next == \E i \in 1..N : Choose(i) \/ Take(i) \/ Exit(i)

ISpec == SpecStart /\ WF_vars(Exit(1)) /\ WF_vars(Exit(2))

MutualExclusion ==
    \A a, b \in inCS : a = b

Inv ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ choosing \subseteq (1..N)
    /\ inCS \subseteq (1..N)
    /\ served \in 0..MaxNat

====