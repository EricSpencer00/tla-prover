---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) == IF c1 = c2 THEN c1
                      ELSE IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN "yellow"
                      ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN "red"
                      ELSE "blue"

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

VARIABLES creature, meetingPlace, totalMeetings

vars == <<creature, meetingPlace, totalMeetings>>

TypeOK ==
    /\ creature \in [Creatures -> [col : Colors, met : 0 .. M]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0 .. M

Init ==
    /\ creature = [c \in Creatures |-> [col |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterPlace(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ creature[c].col # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<creature, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ creature[c].col # Faded
    /\ creature' = [creature EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* The arriving creature and the waiting one, both non-faded, adopt the same
\* new color given by the complement rule and both count the meeting.
Meet(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ creature[c].col # Faded
    /\ creature[meetingPlace].col # Faded
    /\ LET nc == Complement(creature[c].col, creature[meetingPlace].col) IN
         creature' = [creature EXCEPT ![c].col = nc, ![meetingPlace].col = nc,
                      ![c].met = @ + 1, ![meetingPlace].met = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Conservation of meeting participations: a completed meeting is counted once
\* per participant, so the per-creature totals sum to twice the global count.
SumMet == SumOf([c \in Creatures |-> creature[c].met], Creatures)
MeetingConservation == totalMeetings = M => SumMet = 2 * M
====