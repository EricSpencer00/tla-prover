---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* --- banks --------------------------------------------------- *)
East == "East"
West == "West"
Banks == {East, West}

VARIABLES boat, bank

(* --- type invariant ------------------------------------------- *)
TypeOK ==
    /\ boat ∈ Banks
    /\ bank ∈ [Banks -> SUBSET (Missionaries ∪ Cannibals)]
    /\ \A p \in Missionaries ∪ Cannibals :
          (p ∈ bank[East] \/ p ∈ bank[West]) /\ ~(p ∈ bank[East] /\ p ∈ bank[West])

(* --- safety of a single bank ----------------------------------- *)
SafeBank(bset) ==
    LET m == Cardinality(Missionaries ∩ bset)
        c == Cardinality(Cannibals ∩ bset)
    IN (m = 0) \/ (c <= m)

(* --- initial state -------------------------------------------- *)
Init ==
    /\ boat = East
    /\ bank = [b ∈ Banks |-> IF b = East THEN Missionaries ∪ Cannibals ELSE {}]

(* --- next-state relation -------------------------------------- *)
Next ==
    \E grp \subseteq bank[boat] :
        /\ Cardinality(grp) \in {1, 2}
        /\ LET dest == IF boat = East THEN West ELSE East ;
               newBank == [b ∈ Banks |->
                    IF b = boat THEN bank[boat] \ grp
                    ELSE IF b = dest THEN bank[dest] ∪ grp
                    ELSE {}] IN
           /\ boat' = dest
           /\ bank' = newBank
           /\ \A b ∈ Banks : SafeBank(newBank[b])

(* --- solution invariant (violated when solved) --------------- *)
Solution == bank[East] # {}

(* --- optional overall specification --------------------------- *)
Spec == Init /\ [][Next]_<<boat, bank>>

(* --- assumptions about the constants --------------------------- *)
ASSUME /\ Cardinality(Missionaries) = 3
       /\ Cardinality(Cannibals) = 3
       /\ Missionaries ∩ Cannibals = {}

====