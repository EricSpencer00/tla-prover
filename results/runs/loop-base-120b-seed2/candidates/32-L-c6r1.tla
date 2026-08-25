---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ------------------------------------------------------------------- *)
(*  Derived sets *)
Creatures == 1 .. N
NonFadedColors == {"blue", "red", "yellow"}
Colors == NonFadedColors \cup {Faded}

(* ------------------------------------------------------------------- *)
(*  Complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE col \in (NonFadedColors \ {c1, c2}) : TRUE

(* ------------------------------------------------------------------- *)
(*  Variables *)
VARIABLES creatureState, meetingPlace, total

(* ------------------------------------------------------------------- *)
(*  Initial state *)
Init ==
  /\ creatureState = [c \in Creatures |-> 
        [color |-> CHOOSE col \in NonFadedColors : TRUE,
         count |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total = 0

(* ------------------------------------------------------------------- *)
(*  Actions *)

Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ creatureState[c].color # Faded
        /\ meetingPlace' = c
        /\ creatureState' = creatureState
        /\ total' = total

Fade ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total >= M
  /\ \E c \in Creatures :
        /\ creatureState[c].color # Faded
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ creatureState' = [creatureState EXCEPT ![c].color = Faded]
        /\ total' = total

Meet ==
  LET w == meetingPlace IN
    /\ w # MeetingPlaceEmpty
    /\ total < M
    /\ creatureState[w].color # Faded
    /\ \E c \in Creatures :
          /\ c # w
          /\ creatureState[c].color # Faded
          /\ LET newColor == Complement(creatureState[w].color,
                                         creatureState[c].color) IN
               /\ creatureState' = [creatureState EXCEPT 
                                      ![w] = [color |-> newColor,
                                              count |-> creatureState[w].count + 1],
                                      ![c] = [color |-> newColor,
                                              count |-> creatureState[c].count + 1]]
               /\ total' = total + 1
               /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ Enter
  \/ Fade
  \/ Meet

(* ------------------------------------------------------------------- *)
(*  Specification *)
Spec == Init /\ [][Next]_<<creatureState, meetingPlace, total>>

(* ------------------------------------------------------------------- *)
(*  Invariants *)

TypeOK ==
  /\ creatureState \in [Creatures -> [color : Colors, count : Nat]]
  /\ meetingPlace \in Creatures \/ {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total = M) => 
    (Sum({ creatureState[c].count : c \in Creatures }) = 2 * M)

====