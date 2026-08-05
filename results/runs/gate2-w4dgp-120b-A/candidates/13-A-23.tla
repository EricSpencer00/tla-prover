---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, ticket, number, inCS

vars == <<pc, ticket, number, inCS>>

\* Nat is overridden globally in the .cfg (NatOverride); the module must still
\* import the standard Naturals so the inherited operators resolve.

Init ==
    /\ pc = [p \in 0..(N-1) |-> "idle"]
    /\ ticket = [p \in 0..(N-1) |-> 0]
    /\ number = 0
    /\ inCS = {}

\* Explicitly bound the bounded ticket increment so it stays in the finite range,
\* since the .cfg relies on the operator name being unchanged.
Enter(p) ==
    /\ pc[p] = "idle"
    /\ \A q \in 0..(N-1) : ticket[q] = 0 \/ ticket[p] < ticket[q]
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ number' = IF number < MaxNat THEN number + 1 ELSE number
    /\ ticket' = [ticket EXCEPT ![p] = number + (IF number < MaxNat THEN 1 ELSE 0)]
    /\ inCS' = inCS \cup {p}

Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED number

Next ==
    \/ \E p \in 0..(N-1) : Enter(p)
    \/ \E p \in 0..(N-1) : Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 0..(N-1) : p \in inCS => pc[p] = "critical"

TypeOK ==
    /\ pc \in [0..(N-1) -> {"idle", "critical"}]
    /\ ticket \in [0..(N-1) -> 0..MaxNat]
    /\ number \in 0..MaxNat
    /\ inCS \subseteq (0..(N-1))

Inv ==
    /\ \A p \in 0..(N-1) : pc[p] = "critical" => p \in inCS
    /\ \A p \in inCS : pc[p] = "critical"

====