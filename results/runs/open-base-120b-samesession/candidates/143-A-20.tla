---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatLoc, bank

(* The two river banks *)
Banks == {"East", "West"}

(* Universe of all people *)
Persons == Missionaries \cup Cannibals

(* A bank is safe if it contains no missionaries or the number of
   cannibals does not exceed the number of missionaries. *)
Safe(b) ==
  (Missionaries \cap b = {}) \/
  (Cardinality(Cannibals \cap b) <= Cardinality(Missionaries \cap b))

(* Type correctness invariant *)
TypeOK ==
  /\ boatLoc \in Banks
  /\ bank \in [Banks -> SUBSET Persons]
  /\ Missionaries \subseteq Persons
  /\ Cannibals   \subseteq Persons
  /\ Missionaries \cap Cannibals = {}

(* Initial state: everybody and the boat are on the east bank *)
Init ==
  /\ boatLoc = "East"
  /\ bank = [ "East" |-> Persons,
              "West" |-> {} ]

(* One move: transport 1 or 2 people across, keeping both banks safe *)
Next ==
  /\ \E grp \subseteq bank[boatLoc] :
        /\ Cardinality(grp) = 1 \/ Cardinality(grp) = 2
        /\ LET dest    == IF boatLoc = "East" THEN "West" ELSE "East"
               newBank == [bank EXCEPT
                            ![boatLoc] = bank[boatLoc] \ grp,
                            ![dest]    = bank[dest] \cup grp]
           IN /\ Safe(newBank["East"])
              /\ Safe(newBank["West"])
        /\ boatLoc' = IF boatLoc = "East" THEN "West" ELSE "East"
        /\ bank'    = newBank

(* Invariant used to obtain a solution trace: the east bank must
   remain non‑empty; when it becomes empty the invariant is violated,
   yielding a solution. *)
Solution == bank["East"] # {}

====