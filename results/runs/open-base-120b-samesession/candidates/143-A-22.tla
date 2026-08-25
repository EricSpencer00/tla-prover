---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* -----------------------------------------------------------------
   The two river banks
----------------------------------------------------------------- *)
BankSide == {"East", "West"}

VARIABLES boat, bank

People == Missionaries \cup Cannibals

(* -----------------------------------------------------------------
   Type correctness invariant
----------------------------------------------------------------- *)
TypeOK ==
  /\ boat \in BankSide
  /\ bank \in [BankSide -> SUBSET People]
  /\ UNION {bank[b] : b \in BankSide} = People
  /\ \A b1, b2 \in BankSide : b1 # b2 => bank[b1] \cap bank[b2] = {}

(* -----------------------------------------------------------------
   Safety predicate for a given bank side
----------------------------------------------------------------- *)
Safe(bk, side) ==
  LET m == Cardinality(bk[side] \cap Missionaries)
      c == Cardinality(bk[side] \cap Cannibals)
  IN (m = 0) \/ (c <= m)

(* -----------------------------------------------------------------
   Initial state: everyone on the east bank, boat at east
----------------------------------------------------------------- *)
Init ==
  /\ boat = "East"
  /\ bank = [b \in BankSide |-> IF b = "East" THEN People ELSE {}]

(* -----------------------------------------------------------------
   One crossing of the boat (1 or 2 people, never empty)
----------------------------------------------------------------- *)
Next ==
  \E persons \in SUBSET People :
    /\ persons # {}
    /\ Cardinality(persons) \in 1..2
    /\ persons \subseteq bank[boat]
    /\ LET cur   == boat
           dest  == IF boat = "East" THEN "West" ELSE "East"
           newBk == [bank EXCEPT ![cur] = bank[cur] \ persons,
                               ![dest] = bank[dest] \cup persons]
       IN /\ Safe(newBk, cur)
          /\ Safe(newBk, dest)
          /\ boat' = dest
          /\ bank' = newBk

(* -----------------------------------------------------------------
   Solution reached when the east bank is empty
----------------------------------------------------------------- *)
Solution == bank["East"] = {}

(* -----------------------------------------------------------------
   Optional overall specification (not required by the cfg)
----------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<boat, bank>>

====