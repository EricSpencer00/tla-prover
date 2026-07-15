---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------ *)
(*   Types and auxiliary definitions                                         *)
(* ------------------------------------------------------------------------ *)

People == Missionaries \cup Cannibals
Banks  == {"East", "West"}
Bank   == {"East", "West"}

(* The set of possible boat loads: any non‑empty subset of People of size 1 or 2 *)
BoatLoads == { S \in SUBSET People : 1 <= Cardinality(S) /\ Cardinality(S) <= 2 }

(* ------------------------------------------------------------------------ *)
(*   Variables                                                               *)
(* ------------------------------------------------------------------------ *)

VARIABLES boatAt, onBank

(* ------------------------------------------------------------------------ *)
(*   Type invariant (used for the TypeOK invariant)                         *)
(* ------------------------------------------------------------------------ *)

TypeOk ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]
    /\ onBank["East"] \cup onBank["West"] = People
    /\ onBank["East"] \cap onBank["West"] = {}

(* ------------------------------------------------------------------------ *)
(*   Initial state                                                          *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ boatAt = "East"
    /\ onBank["East"] = People
    /\ onBank["West"] = {}

(* ------------------------------------------------------------------------ *)
(*   Safety predicate for a single bank                                      *)
(* ------------------------------------------------------------------------ *)

SafeBank(b) ==
    LET m == Cardinality( onBank[b] \cap Missionaries )
        c == Cardinality( onBank[b] \cap Cannibals )
    IN  (m = 0) \/ (c <= m)

(* ------------------------------------------------------------------------ *)
(*   Safety of the whole configuration                                       *)
(* ------------------------------------------------------------------------ *)

Safe == /\ SafeBank("East") /\ SafeBank("West")

(* ------------------------------------------------------------------------ *)
(*   Boat crossing action (Move)                                            *)
(* ------------------------------------------------------------------------ *)

Move ==
    \E load \in BoatLoads :
        /\ load \subseteq onBank[boatAt]               \* all boarders are on the current bank
        /\ boatAt = "East"
        /\ LET newEast == (onBank["East"] \ load)
               newWest == (onBank["West"] \cup load) IN
           /\ boatAt' = "West"
           /\ onBank' = [onBank EXCEPT !["East"] = newEast,
                                     !"West"] = newWest]
           /\ Safe

    \/ \E load \in BoatLoads :
        /\ load \subseteq onBank[boatAt]               \* all boarders are on the current bank
        /\ boatAt = "West"
        /\ LET newWest == (onBank["West"] \ load)
               newEast == (onBank["East"] \cup load) IN
           /\ boatAt' = "East"
           /\ onBank' = [onBank EXCEPT !["West"] = newWest,
                                     !"East"] = newEast]
           /\ Safe

(* ------------------------------------------------------------------------ *)
(*   Next-state relation                                                    *)
(* ------------------------------------------------------------------------ *)

Next == Move

(* ------------------------------------------------------------------------ *)
(*   Invariants                                                              *)
(* ------------------------------------------------------------------------ *)

TypeOK == TypeOk

Solution == \A b \in Banks : SafeBank(b)

(* ------------------------------------------------------------------------ *)
(*   Specification                                                          *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<boatAt, onBank>>

=============================================================================