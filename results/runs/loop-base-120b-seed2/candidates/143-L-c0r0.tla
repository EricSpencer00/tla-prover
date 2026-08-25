---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES BoatPos, Bank

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
BankNames == {"East", "West"}

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

MissionariesOn(bm, b) == { p \in bm[b] : p \in Missionaries }
CannibalsOn(bm, b)   == { p \in bm[b] : p \in Cannibals }

SafeBank(bm, b) ==
    LET m == Cardinality(MissionariesOn(bm, b))
        c == Cardinality(CannibalsOn(bm, b))
    IN (m = 0) \/ (c <= m)

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ BoatPos \in BankNames
    /\ Bank \in [BankNames -> SUBSET (Missionaries \cup Cannibals)]
    /\ (Bank["East"] \cup Bank["West"]) = Missionaries \cup Cannibals
    /\ (Bank["East"] \cap Bank["West"]) = {}

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ BoatPos = "East"
    /\ Bank = [b \in BankNames |-> IF b = "East"
                                   THEN Missionaries \cup Cannibals
                                   ELSE {}]

(* ----------------------------------------------------------------------
   Move action (one or two people cross)
   ---------------------------------------------------------------------- *)
Move ==
    \E G \subseteq Bank[BoatPos] :
        /\ Cardinality(G) \in 1..2
        /\ LET newBank == [b \in BankNames |-> 
                IF b = BoatPos THEN Bank[b] \ G
                ELSE IF b = Opposite(BoatPos) THEN Bank[b] \cup G
                ELSE Bank[b]]
           IN /\ BoatPos' = Opposite(BoatPos)
              /\ Bank' = newBank
              /\ \A b \in BankNames : SafeBank(newBank, b)

Next == Move

(* ----------------------------------------------------------------------
   Solution predicate (used as an invariant; violation yields a solution)
   ---------------------------------------------------------------------- *)
Solution == Bank["East"] # {}

====