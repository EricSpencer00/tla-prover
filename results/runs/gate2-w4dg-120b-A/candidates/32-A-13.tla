---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A chameneos creature: its color and the number of meetings it has
\* participated in.  The meeting place holds at most one waiting creature.
Creature == [color: {Faded, "blue", "red", "yellow"}, met: 0..M]

VARIABLES creatures, meetingPlace, totalMeetings
vars == <<creatures, meetingPlace, totalMeetings>>

\* The third color not present in the pair {@c1, @c2}, or the common color
\* if the two creatures already share it.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET S == {c1, c2} IN ("blue" \cup "red" \cup "yellow") \ S

RECURSIVE SumOfMet(_)
SumOfMet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN creatures[x].met + SumOfMet(S \ {x})

TypeOK ==
    /\ creatures \in [1..N -> Creature]
    /\ meetingPlace \in 1..N \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ creatures = [i \in 1..N |-> [color |-> "blue", met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ creatures[i].color # Faded
    /\ meetingPlace' = i
    /\ UNCHANGED <<creatures, totalMeetings>>

FadeOut(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ creatures[i].color # Faded
    /\ creatures' = [creatures EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet(i) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # i
    /\ totalMeetings < M
    /\ LET c == Complement(creatures[i].color, creatures[meetingPlace].color) IN
        /\ creatures' = [creatures EXCEPT ![i].color = c, ![i].met = @ + 1,
                                          ![meetingPlace].color = c, ![meetingPlace].met = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : FadeOut(i)
    \/ \E i \in 1..N : Meet(i)

Spec == Init /\ [][Next]_vars

\* When the meeting place closes, every creature's meeting count adds up to
\* exactly twice the number of meetings that actually happened.
SumMet == totalMeetings = M => SumOfMet(1..N) = 2 * totalMeetings

====