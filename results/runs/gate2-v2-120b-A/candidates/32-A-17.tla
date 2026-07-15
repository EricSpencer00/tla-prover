---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    N,               \* number of creatures
    M,               \* total number of meetings allowed
    Faded,           \* the special "faded" color
    MeetingPlaceEmpty \* special value indicating the meeting place is empty

(* ------------------------------------------------------------------------- *)
(*  Color definitions                                                       *)
(* ------------------------------------------------------------------------- *)
Colors == {"blue", "red", "yellow"}
AllColors == Colors \cup {Faded}

\* Complement (mutation) rule: given two colors, return the resulting color
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        LET third == {"blue", "red", "yellow"} \ {c1, c2} IN
        CHOOSE x \in third : TRUE

(* ------------------------------------------------------------------------- *)
(*  State variables                                                         *)
(* ------------------------------------------------------------------------- *)
VARIABLES
    state,       \* mapping from creature id to [color: ..., meetCount: ...]
    room,        \* occupant of the meeting place (MeetingPlaceEmpty or id)
    total        \* total number of completed meetings

(* ------------------------------------------------------------------------- *)
(*  Initialization                                                          *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ state = [i \in 1..N |-> [color |-> CHOOSE c \in Colors : TRUE,
                                 meetCount |-> 0]]
    /\ room = MeetingPlaceEmpty
    /\ total = 0

(* ------------------------------------------------------------------------- *)
(*  Helper definitions                                                      *)
(* ------------------------------------------------------------------------- *)
NonFadedCreatures == { i \in 1..N : state[i].color # Faded }

(* ------------------------------------------------------------------------- *)
(*  Actions                                                                 *)
(* ------------------------------------------------------------------------- *)

EnterEmptyPlace ==
    /\ total < M
    /\ room = MeetingPlaceEmpty
    /\ \E i \in NonFadedCreatures :
        /\ i # room
        /\ room' = i
        /\ UNCHANGED << state, total >>

FadeOut ==
    /\ total = M
    /\ room = MeetingPlaceEmpty
    /\ \E i \in NonFadedCreatures :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED << room, total >>

MeetAndMutate ==
    /\ room # MeetingPlaceEmpty
    /\ \E i \in NonFadedCreatures :
        /\ i # room
        /\ LET c1 == state[i].color IN
           LET c2 == state[room].color IN
           LET newColor == Complement(c1, c2) IN
           /\ state' = [state EXCEPT
                ![i].color = newColor,
                ![i].meetCount = @ + 1,
                ![room].color = newColor,
                ![room].meetCount = @ + 1]
        /\ total' = total + 1
        /\ room' = MeetingPlaceEmpty

\* The system allows any of the above actions, as well as stuttering when no
\* progress is possible.
Next ==
    \/ EnterEmptyPlace
    \/ FadeOut
    \/ MeetAndMutate
    \/ UNCHANGED << state, room, total >>

(* ------------------------------------------------------------------------- *)
(*  Specification                                                           *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<state, room, total>>

(* ------------------------------------------------------------------------- *)
(*  Type correctness invariant                                              *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
    /\ state \in [1..N -> [color : AllColors, meetCount : Nat]]
    /\ room \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

(* ------------------------------------------------------------------------- *)
(*  Safety invariant: sum of individual meeting counts equals twice the    *)
(*  total number of meetings, once the limit M is reached.                  *)
(* ------------------------------------------------------------------------- *)
SumMet ==
    /\ total = M
    /\ \A i \in 1..N : state[i].meetCount \in Nat
    /\ total * 2 = Sum_{i \in 1..N} state[i].meetCount

=============================================================================