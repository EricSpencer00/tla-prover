---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. Colors are symbols; a creature that
\* has faded keeps its meeting count but can never enter again.
Colors == {"blue", "red", "yellow", Faded}
AliveColors == {"blue", "red", "yellow"}

VARIABLES colorAndMet, meetingPlace, totalMet

vars == <<colorAndMet, meetingPlace, totalMet>>

TotalMet == colorAndMet[1][2] + colorAndMet[2][2] + colorAndMet[3][2]

\* The complement rule: two partners with different colors both take the third.
Complement(a, b) ==
    IF a = b THEN a
    ELSE LET S == {a, b}
         IN CHOOSE c \in AliveColors : c \notin S

TypeOK ==
    /\ colorAndMet \in [1..N -> [Colors \X 0..M]]
    /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ \E a \in AliveColors, b \in AliveColors, c \in AliveColors :
         colorAndMet = [x \in 1..N |-> IF x = 1 THEN <<a, 0>>
                                      ELSE IF x = 2 THEN <<b, 0>>
                                      ELSE <<c, 0>>]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

EnterMeetingPlace(x) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ colorAndMet[x][1] \in AliveColors
    /\ totalMet < M
    /\ meetingPlace' = x
    /\ UNCHANGED <<colorAndMet, totalMet>>

FadeOut(x) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = M
    /\ colorAndMet[x][1] \in AliveColors
    /\ colorAndMet' = [colorAndMet EXCEPT ![x] = <<Faded, @>>]
    /\ UNCHANGED <<meetingPlace, totalMet>>

MeetAndMutate(x) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # x
    /\ colorAndMet[x][1] \in AliveColors
    /\ LET p2 == meetingPlace
           newc == Complement(colorAndMet[x][1], colorAndMet[p2][1])
       IN /\ colorAndMet' = [colorAndMet EXCEPT ![x] = <<newc, @ + 1>>,
                                          ![p2] = <<newc, @ + 1>>]
    /\ totalMet' = totalMet + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E x \in 1..N : EnterMeetingPlace(x)
    \/ \E x \in 1..N : FadeOut(x)
    \/ \E x \in 1..N : MeetAndMutate(x)

Spec == Init /\ [][Next]_vars

SumMet == totalMet = M => TotalMet = 2 * M

====