---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANT N      \* Number of creatures (positive natural number)
CONSTANT M      \* Total meetings limit (positive natural number)
CONSTANT Faded
CONSTANT MeetingPlaceEmpty

(*--------------------------------------------------------------------
  SETS
--------------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
Creatures == 0..(N-1)

(*--------------------------------------------------------------------
  TYPE DEFINITIONS
--------------------------------------------------------------------*)
Color == {"blue", "red", "yellow", Faded}
Status == [color : Color, count : Nat]

(*--------------------------------------------------------------------
  STATE VARIABLES
--------------------------------------------------------------------*)
VARIABLES
    status,          \* Mapping Creatures -> Status
    meetingPlace,    \* Either MeetingPlaceEmpty or a creature id
    totalMeetings    \* Global meeting counter

(*--------------------------------------------------------------------
  INITIAL STATE
--------------------------------------------------------------------*)
Init ==
    /\ status = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                      count |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

(*--------------------------------------------------------------------
  HELPERS
--------------------------------------------------------------------*)
IsFaded(c) == status[c].color = Faded

Complement(col1, col2) ==
    IF col1 = col2 THEN col1
    ELSE
        CASE col1 = "blue"  /\ col2 = "red"    -> "yellow"
         [] col1 = "red"   /\ col2 = "blue"   -> "yellow"
         [] col1 = "blue"  /\ col2 = "yellow" -> "red"
         [] col1 = "yellow"/\ col2 = "blue"   -> "red"
         [] col1 = "red"   /\ col2 = "yellow"-> "blue"
         [] col1 = "yellow"/\ col2 = "red"   -> "blue"
         [] OTHER -> col1

(*--------------------------------------------------------------------
  ACTIONS
--------------------------------------------------------------------*)
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in Creatures :
        /\ ~IsFaded(c)
        /\ meetingPlace' = c
        /\ status' = status
        /\ totalMeetings' = totalMeetings

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ \E c \in Creatures :
        /\ ~IsFaded(c)
        /\ meetingPlace' = c
        /\ status' = [status EXCEPT ![c].color = Faded]
        /\ totalMeetings' = totalMeetings

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c2 \in Creatures :
        /\ ~IsFaded(c2)
        /\ c2 # meetingPlace
        /\ LET c1 == meetingPlace IN
            /\ status' = [status EXCEPT
                ![c1].color = Complement(status[c1].color, status[c2].color),
                ![c2].color = Complement(status[c1].color, status[c2].color),
                ![c1].count = status[c1].count + 1,
                ![c2].count = status[c2].count + 1]
            /\ meetingPlace' = MeetingPlaceEmpty
            /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

(*--------------------------------------------------------------------
  SPECIFICATION
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<status, meetingPlace, totalMeetings>>

(*--------------------------------------------------------------------
  INVARIANTS
--------------------------------------------------------------------*)
TypeOK ==
    /\ status \in [Creatures -> Status]
    /\ \A c \in Creatures : status[c].color \in Colors
    /\ \A c \in Creatures : status[c].count \in Nat
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

SumMet ==
    /\ totalMeetings = M
    => 2 * totalMeetings = \Sum_{c \in Creatures} status[c].count

=============================================================================