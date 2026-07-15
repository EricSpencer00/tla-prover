---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------- *)
(* Types and helper definitions *)
(* ------------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

Bank == {"East", "West"}

(* The set of all possible groups of 1 or 2 distinct people *)
Groups == { g \in SUBSET People : Cardinality(g) \in 1..2 }

(* Safety condition for a given bank configuration *)
SafeBank(s) == 
    (Cardinality({p \in s : p \in Missionaries}) = 0) \/
    (Cardinality({p \in s : p \in Cannibals}) <= Cardinality({p \in s : p \in Missionaries}))

(* ------------------------------------------------------------------------- *)
(* Variables *)
(* ------------------------------------------------------------------------- *)

VARIABLES BoatAt, PeopleOn

(* PeopleOn is a function mapping each bank to the set of people currently there *)
vars == <<BoatAt, PeopleOn>>

(* ------------------------------------------------------------------------- *)
(* Initial state *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ BoatAt = "East"
    /\ PeopleOn = [b \in Bank |-> 
                    IF b = "East" 
                    THEN Missionaries \cup Cannibals 
                    ELSE {}]

(* ------------------------------------------------------------------------- *)
(* Transition (Next) *)
(* ------------------------------------------------------------------------- *)

Next ==
    \E g \in Groups :
        /\ g \subseteq PeopleOn[BoatAt]               \* they board from current bank
        /\ BoatAt' = IF BoatAt = "East" THEN "West" ELSE "East"
        /\ PeopleOn' = [b \in Bank |-> 
                        IF b = BoatAt 
                        THEN PeopleOn[b] \ SetMinus g          \* left current bank
                        ELSE IF b = BoatAt' 
                             THEN PeopleOn[b] \cup g           \* arrive at opposite bank
                             ELSE PeopleOn[b]]
        /\ SafeBank(PeopleOn'[ "East" ])               \* safety after move
        /\ SafeBank(PeopleOn'[ "West" ])

(* ------------------------------------------------------------------------- *)
(* Specification *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Invariants *)
(* ------------------------------------------------------------------------- *)

(* Type correctness: variables range over the intended domains *)
TypeOK ==
    /\ BoatAt \in Bank
    /\ PeopleOn \in [Bank -> SUBSET People]
    /\ \A b \in Bank : \A p \in PeopleOn[b] : p \in People

(* Safety: both banks are always safe *)
SafeBanks == SafeBank(PeopleOn["East"]) /\ SafeBank(PeopleOn["West"])

(* Solution: the east bank is empty (everyone has crossed) *)
Solution == PeopleOn["East"] = {}

(* The required invariant named Solution must hold in all reachable states *)
Inv_Solution == Solution

(* The required invariant named TypeOK must hold in all reachable states *)
Inv_TypeOK == TypeOK

(* ------------------------------------------------------------------------- *)
(* Theorem (optional, for completeness) *)
(* ------------------------------------------------------------------------- *)

THEOREM Spec => []SafeBanks

=============================================================================