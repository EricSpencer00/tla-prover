---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Derived constants *)
MaxVal == 2 ^ D - 1
DiskSet == { 2 ^ k : k \in 0 .. D - 1 }

(* Helper predicates *)
DiskOn(v, d) == ((v \div d) % 2) = 1
NoSmaller(v, d) == \A e \in DiskSet : e < d => ((v \div e) % 2) = 0

Init ==
    towers = [i \in 1 .. N |-> IF i = 1 THEN MaxVal ELSE 0]

Next ==
    \E d \in DiskSet :
        \E src \in 1 .. N :
            \E dst \in 1 .. N :
                /\ src # dst
                /\ DiskOn(towers[src], d)
                /\ NoSmaller(towers[src], d)
                /\ NoSmaller(towers[dst], d)
                /\ towers' = [i \in 1 .. N |-> 
                        IF i = src THEN towers[i] - d
                        ELSE IF i = dst THEN towers[i] + d
                        ELSE towers[i]]

Spec == Init /\ [] [Next]_towers

TypeOK ==
    \A i \in 1 .. N : towers[i] \in Nat /\ towers[i] <= MaxVal

Total == Sum({ towers[i] : i \in 1 .. N })
Inv == Total = MaxVal

====