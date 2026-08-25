---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(*--- banks ---------------------------------------------------*)
Bank == {"East", "West"}
East == "East"
West == "West"

(*--- state variables ------------------------------------------*)
VARIABLES BoatPos, People

(*--- helpers -------------------------------------------------*)
MissionariesOn(b) == People[b] ∩ Missionaries
CannibalsOn(b)    == People[b] ∩ Cannibals

SafeBank(b) ==
    \/ MissionariesOn(b) = {}
    \/ Cardinality(CannibalsOn(b)) <= Cardinality(MissionariesOn(b))

(*--- type invariant -------------------------------------------*)
TypeOK ==
    /\ BoatPos ∈ Bank
    /\ People ∈ [Bank -> SUBSET (Missionaries ∪ Cannibals)]
    /\ UNION People[Bank] = Missionaries ∪ Cannibals
    /\ \A b1, b2 \in Bank : (b1 # b2) => People[b1] ∩ People[b2] = {}

(*--- initial state -------------------------------------------*)
Init ==
    /\ BoatPos = East
    /\ People = [b \in Bank |-> IF b = East THEN Missionaries ∪ Cannibals ELSE {}]

(*--- move action --------------------------------------------*)
Move ==
    LET cur   == BoatPos
        other == IF cur = East THEN West ELSE East
    IN
    ∃ group ⊆ People[cur] :
        /\ Cardinality(group) ∈ {1, 2}
        /\ BoatPos' = other
        /\ People' = [People EXCEPT
                        ![cur]   = People[cur] \ group,
                        ![other] = People[other] ∪ group]
        /\ ∀ b \in Bank :
               (People'[b] ∩ Missionaries = {})
               \/ Cardinality(People'[b] ∩ Cannibals) <= Cardinality(People'[b] ∩ Missionaries)

(*--- next-state relation --------------------------------------*)
Next == Move

(*--- solution predicate ---------------------------------------*)
Solution == People[East] = {}

====