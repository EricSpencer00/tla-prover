---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET s == {c1, c2} IN CHOOSE c \in Colors \ {Faded} : s = Colors \ {c}

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

VARIABLES creatureState, meetingPlace, totalMeetings

TypeOK ==
    /\ creatureState \in [Creatures -> [color : Colors, met : 0..(2 * M)]]
    /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
    /\ totalMeetings \in 0..M

Init ==
    /\ \E c \in [Creatures -> Colors] :
         /\ \A i \in Creatures : creatureState[i].color \in {"blue", "red", "yellow"}
         /\ \A i \in Creatures : creatureState[i].met = 0
         /\ creatureState = [i \in Creatures |-> [color |-> c[i], met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ creatureState[i].color # Faded
    /\ meetingPlace' = i
    /\ UNCHANGED <<creatureState, totalMeetings>>

Fade(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ creatureState[i].color # Faded
    /\ creatureState' = [creatureState EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet(i) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # i
    /\ creatureState[i].color # Faded
    /\ creatureState[meetingPlace].color # Faded
    /\ totalMeetings < M
    /\ LET newColor == Complement(creatureState[i].color, creatureState[meetingPlace].color) IN
         creatureState' = [creatureState EXCEPT
                             ![i].color = newColor,
                             ![i].met = @ + 1,
                             ![meetingPlace].color = newColor,
                             ![meetingPlace].met = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E i \in Creatures : Enter(i)
    \/ \E i \in Creatures : Fade(i)
    \/ \E i \in Creatures : Meet(i)

Spec == Init /\ [][Next]_<<creatureState, meetingPlace, totalMeetings>>

SumMet ==
    (totalMeetings = M) => (SumOf([i \in Creatures |-> creatureState[i].met], Creatures) = 2 * M)

====