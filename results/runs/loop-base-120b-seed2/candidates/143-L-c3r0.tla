---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, eastBank, westBank

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
   /\ boat \in {"East", "West"}
   /\ eastBank \subseteq People
   /\ westBank \subseteq People
   /\ eastBank \cup westBank = People
   /\ eastBank \cap westBank = {}

(* ----------------------------------------------------------------------
   Safety condition for a single bank
   ---------------------------------------------------------------------- *)
SafeBank(b) ==
   \/ b \cap Missionaries = {}
   \/ Cardinality(b \cap Cannibals) <= Cardinality(b \cap Missionaries)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
   /\ boat = "East"
   /\ eastBank = People
   /\ westBank = {}

(* ----------------------------------------------------------------------
   One crossing of the boat
   ---------------------------------------------------------------------- *)
Move ==
   LET srcBank == IF boat = "East" THEN eastBank ELSE westBank
       dstBank == IF boat = "East" THEN westBank ELSE eastBank IN
   \E g \in SUBSET srcBank :
       /\ 1 <= Cardinality(g) /\ Cardinality(g) <= 2
       /\ LET newSrc == srcBank \ g
              newDst == dstBank \cup g IN
          /\ SafeBank(newSrc) /\ SafeBank(newDst)
          /\ boat' = IF boat = "East" THEN "West" ELSE "East"
          /\ eastBank' = IF boat = "East" THEN newSrc ELSE newDst
          /\ westBank' = IF boat = "East" THEN newDst ELSE newSrc

Next == Move

(* ----------------------------------------------------------------------
   Goal condition (solution)
   ---------------------------------------------------------------------- *)
Solution == eastBank = {}

=============================================================================