---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Types and constants                                                    *)
(* ---------------------------------------------------------------------- *)

Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

(* ---------------------------------------------------------------------- *)
(* Variables                                                              *)
(* ---------------------------------------------------------------------- *)

VARIABLES 
    colors,          \* [creature -> color]
    meetCounts,      \* [creature -> Nat]
    meetingPlace,    \* either MeetingPlaceEmpty or a creature identifier
    totalMeetings    \* Nat, number of completed meetings

(* ---------------------------------------------------------------------- *)
(* Helper definitions                                                    *)
(* ---------------------------------------------------------------------- *)

Creatures == 1..N

InitColors == 
    [c \in Creatures |-> CHOOSE col \in NonFadedColors : TRUE]

InitMeetCounts ==
    [c \in Creatures |-> 0]

InitMeetingPlace ==
    MeetingPlaceEmpty

InitTotalMeetings == 0

(* ---------------------------------------------------------------------- *)
(* Complement rule                                                       *)
(* ---------------------------------------------------------------------- *)

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        LET third == { "blue", "red", "yellow" } \ {c1, c2} IN
            CHOOSE col \in third : TRUE

(* ---------------------------------------------------------------------- *)
(* Initial predicate                                                      *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ colors = InitColors
    /\ meetCounts = InitMeetCounts
    /\ meetingPlace = InitMeetingPlace
    /\ totalMeetings = InitTotalMeetings

(* ---------------------------------------------------------------------- *)
(* Actions                                                                *)
(* ---------------------------------------------------------------------- *)

EnterEmptyPlace ==
    /\ totalMeetings < M
    /\ meetingPlace = MeetingPlaceEmpty
    /\ \E c \in Creatures :
        /\ colors[c] # Faded
        /\ meetingPlace' = c
        /\ UNCHANGED << colors, meetCounts, totalMeetings >>

FadeOut ==
    /\ totalMeetings >= M
    /\ meetingPlace = MeetingPlaceEmpty
    /\ \E c \in Creatures :
        /\ colors[c] # Faded
        /\ colors' = [colors EXCEPT ![c] = Faded]
        /\ UNCHANGED << meetCounts, meetingPlace, totalMeetings >>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c1 \in Creatures :
        /\ c1 # meetingPlace
        /\ colors[c1] # Faded
        /\ LET c2 == meetingPlace IN
            /\ colors' = [colors EXCEPT 
                         ![c1] = Complement(colors[c1], colors[c2]),
                         ![c2] = Complement(colors[c1], colors[c2])]
            /\ meetCounts' = [meetCounts EXCEPT 
                              ![c1] = @ + 1,
                              ![c2] = @ + 1]
            /\ totalMeetings' = totalMeetings + 1
            /\ meetingPlace' = MeetingPlaceEmpty

NoOp ==
    UNCHANGED << colors, meetCounts, meetingPlace, totalMeetings >>

Next ==
    \/ EnterEmptyPlace
    \/ FadeOut
    \/ MeetAndMutate
    \/ NoOp

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<colors, meetCounts, meetingPlace, totalMeetings>>

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant                                             *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ colors \in [Creatures -> Colors]
    /\ meetCounts \in [Creatures -> Nat]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

(* ---------------------------------------------------------------------- *)
(* Safety invariant: sum of individual meeting counts equals twice the   *)
(* total number of meetings once the limit is reached.                    *)
(* ---------------------------------------------------------------------- *)

SumMet ==
    /\ totalMeetings >= M
    /\ \A c \in Creatures : meetCounts[c] <= M
    /\ ( \A c \in Creatures : meetCounts[c] >= 0 )
    /\ ( \A c \in Creatures : colors[c] # Faded => meetCounts[c] >= 0 )
    /\ ( \E c \in Creatures : colors[c] = Faded => TRUE ) \* no restriction
    /\ ( \A c \in Creatures : colors[c] = Faded => TRUE ) \* placeholder
    /\ ( \A c \in Creatures : colors[c] # Faded => TRUE ) \* placeholder
    /\ ( \A c \in Creatures : colors[c] \in NonFadedColors \/ colors[c] = Faded )
    /\ ( \A c \in Creatures : meetCounts[c] \in Nat )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ ( \A c \in Creatures : colors[c] \in Colors )
    /\ Sum(meetCounts) = 2 * totalMeetings

=============================================================================