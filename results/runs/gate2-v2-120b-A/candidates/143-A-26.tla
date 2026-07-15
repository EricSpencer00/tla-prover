---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------- *)
(*  Derived sets                                                             *)
(* ------------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

(* ------------------------------------------------------------------------- *)
(*  State variables                                                         *)
(* ------------------------------------------------------------------------- *)
VARIABLES BoatPos, EastBank, WestBank

(* ------------------------------------------------------------------------- *)
(*  Initial state                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ BoatPos = "East"
    /\ EastBank = People
    /\ WestBank = {}

(* ------------------------------------------------------------------------- *)
(*  Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)
BankPeople(b) == IF b = "East" THEN EastBank ELSE WestBank

OtherBank(b) == IF b = "East" THEN "West" ELSE "East"

(* Safety condition for a given set of people on a bank *)
Safe(s) ==
    LET M == Cardinality(Missionaries \cap s) IN
    LET C == Cardinality(Cannibals \cap s) IN
    (M = 0) \/ (C <= M)

(* The set of possible groups (1 or 2 people) that can board the boat *)
PossibleGroups(b) ==
    { g \in SUBSET BankPeople(b) :
        /\ Cardinality(g) \in 1..2
        /\ g # {} }

(* Update the distribution of people after moving group g from bank b *)
UpdateBanks(b, g) ==
    IF b = "East" THEN
        [ EastBank |-> EastBank \ g,
          WestBank |-> WestBank \cup g ]
    ELSE
        [ EastBank |-> EastBank \cup g,
          WestBank |-> WestBank \ g ]

(* ------------------------------------------------------------------------- *)
(*  Move action: one group crosses the river                               *)
(* ------------------------------------------------------------------------- *)
Move ==
    \E g \in PossibleGroups(BoatPos) :
        LET newBanks == UpdateBanks(BoatPos, g) IN
        /\ Safe(newBanks["East"])
        /\ Safe(newBanks["West"])
        /\ BoatPos' = OtherBank(BoatPos)
        /\ EastBank' = newBanks["East"]
        /\ WestBank' = newBanks["West"]
        /\ UNCHANGED << >>

(* ------------------------------------------------------------------------- *)
(*  Next-state relation                                                      *)
(* ------------------------------------------------------------------------- *)
Next == Move

(* ------------------------------------------------------------------------- *)
(*  Type correctness invariant                                               *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ BoatPos \in {"East", "West"}
    /\ EastBank \subseteq People
    /\ WestBank \subseteq People
    /\ EastBank \cup WestBank = People
    /\ EastBank \cap WestBank = {}

(* ------------------------------------------------------------------------- *)
(*  Safety invariant: solution condition (east bank empty)                 *)
(* ------------------------------------------------------------------------- *)
Solution == EastBank = {}

=============================================================================