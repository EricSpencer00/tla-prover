---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* --------------------------------------------------------------------- *)
(* Universe of persons *)
Persons == Missionaries \cup Cannibals

(* --------------------------------------------------------------------- *)
(* Variables *)
VARIABLES BoatPos, Bank

(* --------------------------------------------------------------------- *)
(* Type correctness *)

TypeOK ==
    /\ BoatPos \in {"East", "West"}
    /\ Bank \in [ {"East", "West"} -> SUBSET Persons ]
    /\ Bank["East"] \cup Bank["West"] = Persons
    /\ Bank["East"] \cap Bank["West"] = {}

(* --------------------------------------------------------------------- *)
(* Safety of a bank given a set of people on it *)

SafeBankOn(bSet) ==
    LET m == Cardinality({ p \in bSet : p \in Missionaries })
        c == Cardinality({ p \in bSet : p \in Cannibals })
    IN (m = 0) \/ (c <= m)

(* --------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ BoatPos = "East"
    /\ Bank = [b \in {"East","West"} |-> IF b = "East" THEN Persons ELSE {}]

(* --------------------------------------------------------------------- *)
(* Helper: opposite bank *)

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

(* --------------------------------------------------------------------- *)
(* Next-state relation: move one or two people across *)

Next ==
    \E g \subseteq Bank[BoatPos] :
        /\ Cardinality(g) \in 1..2
        /\ LET newBank ==
                IF BoatPos = "East"
                THEN [ "East" |-> Bank["East"] \ g,
                       "West" |-> Bank["West"] \cup g ]
                ELSE [ "East" |-> Bank["East"] \cup g,
                       "West" |-> Bank["West"] \ g ]
           IN /\ SafeBankOn(newBank["East"])
              /\ SafeBankOn(newBank["West"])
              /\ BoatPos' = Opposite(BoatPos)
              /\ Bank' = newBank

(* --------------------------------------------------------------------- *)
(* Specification *)

vars == <<BoatPos, Bank>>

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Invariants *)

Solution == Bank["East"] = {}

(* --------------------------------------------------------------------- *)

====