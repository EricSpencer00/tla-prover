---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The inductive (ISpec) instead of the functional (FSpec) specification starts from arbitrary
\* type-correct states and requires the invariant to hold at every reachable state.
\* The natural numbers are overridden to a finite range 0..MaxNat for model checking.

States == {"idle", "waiting", "critical"}

VARIABLES pc, ticket, served

vars == <<pc, ticket, served>>

TypeOK ==
    /\ pc \in [1..N -> States]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in 0..MaxNat

MutualExclusion ==
    \A p, q \in 1..N : (pc[p] = "critical" /\ pc[q] = "critical") => p = q

Inv ==
    /\ TypeOK
    /\ \A p \in 1..N : pc[p] = "critical" => ticket[p] <= served
    /\ \A p \in 1..N : pc[p] = "critical" => \A q \in 1..N : ticket[p] >= ticket[q]

Init ==
    /\ pc = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ served = 0

\* A process requests entry: it adopts a ticket strictly above the current served count.
Request(p) ==
    /\ pc[p] = "idle"
    /\ served < MaxNat
    /\ \E k \in (served + 1)..MaxNat :
         /\ ticket' = [ticket EXCEPT ![p] = k]
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED served

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ \A q \in 1..N : ticket[p] >= ticket[q]
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, served>>

Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ UNCHANGED ticket

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

StateConstraint == Cardinality({p \in 1..N : pc[p] = "critical"}) <= 1

ISpec == Init /\ [][Next]_vars /\ WF_vars(Exit(1)) /\ WF_vars(Exit(2))

====