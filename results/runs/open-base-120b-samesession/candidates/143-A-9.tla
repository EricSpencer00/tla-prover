---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------- *)
(* Banks *)
East == "East"
West == "West"
Banks == {East, West}

(* ------------------------------------------------------------------------- *)
(* Variables *)
VARIABLES boat, people

(* ------------------------------------------------------------------------- *)
(* Helper definitions *)

IsMissionary(p) == p \in Missionaries
IsCannibal(p)   == p \in Cannibals

MissionariesOn(s) == { p \in s : IsMissionary(p) }
CannibalsOn(s)   == { p \in s : IsCannibal(p) }

SafeSet(s) == 
    (MissionariesOn(s) = {}) \/ 
    (Cardinality(CannibalsOn(s)) <= Cardinality(MissionariesOn(s)))

Safe(b) == SafeSet(people[b])

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant *)

TypeOK ==
    /\ boat \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ (people[East] \cup people[West]) = Missionaries \cup Cannibals
    /\ (people[East] \cap people[West]) = {}

(* ------------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ boat = East
    /\ people = [East |-> Missionaries \cup Cannibals,
                West |-> {}]

(* ------------------------------------------------------------------------- *)
(* Move action *)

Move ==
    \E grp \in SUBSET people[boat] :
        /\ Cardinality(grp) \in 1..2
        /\ LET other == IF boat = East THEN West ELSE East IN
               /\ boat' = other
               /\ people' = [people EXCEPT 
                               ![boat] = people[boat] \ grp,
                               ![other] = people[other] \cup grp]
               /\ SafeSet(people'[boat])       \* safety after departure bank
               /\ SafeSet(people'[other])      \* safety after arrival bank

Next == Move

(* ------------------------------------------------------------------------- *)
(* Solution invariant: all persons have reached the West bank *)

Solution == people[East] = {}

(* ------------------------------------------------------------------------- *)
(* Specification (optional, not required by the cfg) *)

Spec == Init /\ [][Next]_<<boat,people>>

====