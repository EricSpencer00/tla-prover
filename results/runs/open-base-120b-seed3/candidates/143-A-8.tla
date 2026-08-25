---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, Banks

(* derived sets *)
People   == Missionaries \cup Cannibals
BankSide == {"East", "West"}

(* A bank is safe if it contains no missionaries, or the number of
   cannibals does not exceed the number of missionaries. *)
Safe(b) ==
  \A side \in BankSide :
    LET m == Cardinality(b[side] \cap Missionaries) ;
        c == Cardinality(b[side] \cap Cannibals) ;
    IN (m = 0) \/ (c <= m)

(* Initial state: all people on the east bank, boat docked at east. *)
Init ==
  /\ boat = "East"
  /\ Banks = [s \in BankSide |-> IF s = "East" THEN People ELSE {}]

(* One move: choose 1 or 2 people from the current bank, cross to the other,
   and keep the resulting configuration safe. *)
Move ==
  \E grp \in SUBSET (Banks[boat]) :
    /\ Cardinality(grp) \in {1, 2}
    /\ LET other    == IF boat = "East" THEN "West" ELSE "East" ;
           newBanks == [Banks EXCEPT ![boat] = Banks[boat] \ grp,
                                    ![other] = Banks[other] \cup grp]
       IN /\ boat'   = other
          /\ Banks'  = newBanks
          /\ Safe(newBanks)

Next == Move

(* Type correctness of the state variables. *)
TypeOK ==
  /\ boat \in BankSide
  /\ Banks \in [BankSide -> SUBSET People]
  /\ \A s \in BankSide : Banks[s] \subseteq People
  /\ Banks["East"] \cap Banks["West"] = {}
  /\ People = Banks["East"] \cup Banks["West"]

(* Invariant used to locate a solution: the east bank must remain non‑empty.
   When the model checker discovers a violation, the east bank is empty,
   meaning the puzzle is solved. *)
Solution == Banks["East"] # {}

====