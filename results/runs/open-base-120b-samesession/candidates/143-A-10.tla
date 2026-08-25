---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, bank

(* ------------------------------------------------------------------------ *)
(* Basic sets *)

People == Missionaries \cup Cannibals
Sides  == {"East", "West"}

(* ------------------------------------------------------------------------ *)
(* Helper definitions *)

MSet(b) == { x \in b : x \in Missionaries }
CSet(b) == { x \in b : x \in Cannibals }

SafeSide(b) ==
    \/ MSet(b) = {}
    \/ Cardinality(CSet(b)) <= Cardinality(MSet(b))

(* ------------------------------------------------------------------------ *)
(* Type invariant (includes safety) *)

TypeOK ==
    /\ boat \in Sides
    /\ bank \in [Sides -> SUBSET People]
    /\ bank["East"] \cup bank["West"] = People
    /\ bank["East"] \cap bank["West"] = {}
    /\ SafeSide(bank["East"])
    /\ SafeSide(bank["West"])

(* ------------------------------------------------------------------------ *)
(* Initial state *)

Init ==
    /\ boat = "East"
    /\ bank = [ s \in Sides |-> IF s = "East" THEN People ELSE {} ]

(* ------------------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
    \E g \subseteq bank[boat] :
        /\ Cardinality(g) \in 1..2
        /\ LET other == IF boat = "East" THEN "West" ELSE "East"
               newBank == [bank EXCEPT ![boat] = bank[boat] \ g,
                                      ![other] = bank[other] \cup g]
           IN /\ boat' = other
              /\ bank' = newBank
              /\ SafeSide(newBank["East"])
              /\ SafeSide(newBank["West"])

(* ------------------------------------------------------------------------ *)
(* Invariant expressing the goal (the east bank must stay non‑empty) *)

Solution == bank["East"] # {}

(* ------------------------------------------------------------------------ *)
(* Specification (optional, but useful) *)

Spec == Init /\ [][Next]_<<boat, bank>>

==============================================================================