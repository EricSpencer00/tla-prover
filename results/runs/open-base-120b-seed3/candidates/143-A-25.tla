---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Banks
   ---------------------------------------------------------------------- *)
Bank == {"East", "West"}
East == "East"
West == "West"

Opposite(b) == IF b = East THEN West ELSE East

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES BoatAt, People

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ BoatAt \in Bank
  /\ People \in [Bank -> SUBSET (Missionaries \cup Cannibals)]
  /\ UNION People = Missionaries \cup Cannibals
  /\ \A b \in Bank : People[b] \cap People[Opposite(b)] = {}

(* ----------------------------------------------------------------------
   Safety of a single bank
   ---------------------------------------------------------------------- *)
SafeBank(b) ==
  LET m == Cardinality(Missionaries \cap People[b])
      c == Cardinality(Cannibals \cap People[b])
  IN (m = 0) \/ (c <= m)

Safe == \A b \in Bank : SafeBank(b)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ BoatAt = East
  /\ People = [East |-> Missionaries \cup Cannibals,
               West |-> {}]

(* ----------------------------------------------------------------------
   Move action (one or two people cross)
   ---------------------------------------------------------------------- *)
Move ==
  \E moving \in SUBSET People[BoatAt] :
    /\ Cardinality(moving) \in 1..2
    /\ BoatAt' = Opposite(BoatAt)
    /\ People' = [People EXCEPT
          ![BoatAt] = People[BoatAt] \ moving,
          ![Opposite(BoatAt)] = People[Opposite(BoatAt)] \cup moving]
    /\ Safe'

Next == Move

(* ----------------------------------------------------------------------
   Solution invariant (east bank empty)
   ---------------------------------------------------------------------- *)
Solution == People[East] = {}

====