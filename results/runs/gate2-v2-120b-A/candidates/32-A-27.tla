---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

***************************************************************************
(*  Constants (to be set in the .cfg file)                               *)
***************************************************************************
CONSTANT N          \* number of creatures (>= 1)
CONSTANT M          \* total meeting limit (>= 1)
CONSTANT Faded      \* the special color indicating a faded creature
CONSTANT MeetingPlaceEmpty \* the value indicating an empty meeting place

\* Derived constant: set of creature identifiers
Creatures == 1 .. N

\* Set of possible colors (including the faded state)
Colors == {"blue", "red", "yellow", Faded}

\* The special "empty" identifier for the meeting place
MeetingPlaceEmpty \in Creatures \cup {MeetingPlaceEmpty}

\* Helper: the set of non‑faded colors
NonFadedColors == {"blue", "red", "yellow"}

***************************************************************************
(*  State variables                                                       *)
***************************************************************************
VARIABLES
    state,          \* mapping from each creature to a record [color, met]
    meetingPlace,   \* either MeetingPlaceEmpty or a creature id
    totalMet        \* total number of completed meetings

\* Record type for each creature's local state
CreatureRec == [color : Colors, met : Nat]

\* Initial assignment
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in NonFadedColors : TRUE,
                                     met   |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

***************************************************************************
(*  Color complement rule                                                 *)
***************************************************************************
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE
            c1 = "blue"  /\ c2 = "red"    -> "yellow" ;
            c1 = "red"   /\ c2 = "blue"   -> "yellow" ;
            c1 = "blue"  /\ c2 = "yellow" -> "red"    ;
            c1 = "yellow" /\ c2 = "blue"  -> "red"    ;
            c1 = "red"   /\ c2 = "yellow"-> "blue"   ;
            c1 = "yellow" /\ c2 = "red"   -> "blue"   ;
            OTHER -> "blue" \* unreachable but required for totality
        ENDCASE

***************************************************************************
(*  Actions                                                               *)
***************************************************************************
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ meetingPlace' = c
          /\ UNCHANGED << state, totalMet >>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED << meetingPlace, totalMet >>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ totalMet < M
    /\ \E cNew \in Creatures :
          /\ state[cNew].color # Faded
          /\ cNew # meetingPlace
          /\ LET cOld == meetingPlace IN
                /\ newColor == Complement(state[cNew].color, state[cOld].color)
                /\ state' = [state EXCEPT
                                 ![cNew].color = newColor,
                                 ![cNew].met   = @ + 1,
                                 ![cOld].color = newColor,
                                 ![cOld].met   = @ + 1]
                /\ totalMet' = totalMet + 1
                /\ meetingPlace' = MeetingPlaceEmpty
                /\ UNCHANGED << >>

\* Stuttering step to keep the model total when no other action is enabled
Idle ==
    UNCHANGED << state, meetingPlace, totalMet >>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Idle

Spec == Init /\ [][Next]_<<state, meetingPlace, totalMet>>

***************************************************************************
(*  Type correctness invariant                                            *)
***************************************************************************
TypeOK ==
    /\ state \in [Creatures -> CreatureRec]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in Nat

\* Alias required by the .cfg file
Spec == Spec

\* Safety invariant: sum of individual meetings equals twice total meetings
SumMet ==
    /\ totalMet <= M
    /\ totalMet = (1/2) * (+\c \in Creatures : state[c].met)

=============================================================================