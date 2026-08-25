---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES BoatAt, EastBank

(* ----------------------------------------------------------------------
   Derived definitions
   ---------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

IsMissionary(p) == p \in Missionaries
IsCannibal(p)   == p \in Cannibals

MissionariesIn(s) == { p \in s : IsMissionary(p) }
CannibalsIn(s)    == { p \in s : IsCannibal(p) }

Safe(s) ==
  \/ Cardinality(MissionariesIn(s)) = 0
  \/ Cardinality(CannibalsIn(s)) <= Cardinality(MissionariesIn(s))

(* ----------------------------------------------------------------------
   Type correctness and safety invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
  /\ BoatAt \in {"East","West"}
  /\ EastBank \subseteq People
  /\ Safe(EastBank)
  /\ Safe(People \ EastBank)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
  /\ BoatAt = "East"
  /\ EastBank = People

(* ----------------------------------------------------------------------
   Move action (boat carries 1 or 2 people)
   ---------------------------------------------------------------------- *)

Move ==
  \E persons \in SUBSET (IF BoatAt = "East" THEN EastBank ELSE People \ EastBank) :
    /\ Cardinality(persons) \in {1,2}
    /\ LET newEastBank ==
           IF BoatAt = "East"
              THEN EastBank \ persons
              ELSE EastBank \cup persons
       IN
          /\ Safe(newEastBank)
          /\ Safe(People \ newEastBank)
          /\ BoatAt' = (IF BoatAt = "East" THEN "West" ELSE "East")
          /\ EastBank' = newEastBank

Next == Move

(* ----------------------------------------------------------------------
   Solution invariant (the east bank must stay non‑empty; its violation
   yields a solution trace)
   ---------------------------------------------------------------------- *)

Solution == EastBank /= {}

=============================================================================