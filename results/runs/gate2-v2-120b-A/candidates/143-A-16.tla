---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Missionaries, Cannibals

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES boat, where   \* boat : set of People on the boat (transit)
                         \* where : "East" or "West", the bank where the boat is docked

(*--------------------------------------------------------------------
  Type correctness
--------------------------------------------------------------------*)
TypeOK ==
    /\ boat \subseteq People
    /\ where \in Banks
    /\ \A b \in Banks: b \subseteq People

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ boat = {}
    /\ where = "East"
    /\ Missionaries \subseteq People
    /\ Cannibals \subseteq People
    /\ Missionaries \cap Cannibals = {}
    /\ \A p \in People: p \in Missionaries \/ p \in Cannibals

(*--------------------------------------------------------------------
  Helper predicates
--------------------------------------------------------------------*)
SafeBank(b) ==
    LET M == {p \in b : p \in Missionaries}
        C == {p \in b : p \in Cannibals}
    IN  (M = {} \/ Cardinality(C) <= Cardinality(M))

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Move ==
    \E passengers \subseteq People :
        /\ Cardinality(passengers) \in 1..2
        /\ passengers \subseteq (IF where = "East" THEN Missionaries \cup Cannibals ELSE {})
        /\ boat' = passengers
        /\ where' = IF where = "East" THEN "West" ELSE "East"
        /\ UNCHANGED <<>>  \* no other variables change in this step

Cross ==
    \E passengers == boat :
        /\ passengers' = {}
        /\ LET newEast == IF where = "East"
                           THEN Missionaries \cup Cannibals \ {p \in passengers}
                           ELSE Missionaries \cup Cannibals
           newWest == IF where = "West"
                           THEN Missionaries \cup Cannibals \ {p \in passengers}
                           ELSE Missionaries \cup Cannibals
        IN  /\ SafeBank(newEast)
            /\ SafeBank(newWest)
        /\ UNCHANGED where

Next ==
    \/ Move
    \/ Cross

(*--------------------------------------------------------------------
  Safety invariant (the one named Solution)
--------------------------------------------------------------------*)
Solution ==
    SafeBank(Missionaries \cup Cannibals)   \* safety on the whole set

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<boat, where>>

=============================================================================