---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature identifiers are numbers 1..N; colors are a small cyclic set.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
kinds == {"blue", "red", "yellow"}

\* The complement rule: a meeting of two different colors yields the third.
Complement(x, y) ==
    IF x = y THEN x
    ELSE IF {"blue", "red", "yellow"} \ {x, y} = {} THEN x
    ELSE CHOOSE z \in kinds : z \notin {x, y}

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE
         IN f[x] + SumOf(f, S \ {x})

VARIABLES state, meetingPlace, totalMeetings

vars == <<state, meetingPlace, totalMeetings>>

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, mcount: 0..M]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE k \in kinds : TRUE, mcount |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings = M
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ totalMeetings < M
    /\ LET other == meetingPlace
           newcol == Complement(state[c].color, state[other].color)
       IN /\ state' = [state EXCEPT ![c].color = newcol, ![c].mcount = @ + 1,
                                      ![other].color = newcol, ![other].mcount = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Each meeting consumes two participant slots, so at the limit the two counts
\* must account for exactly twice the limit's worth of participations.
BoundedMeetingSum == (totalMeetings = M) => SumOf([c \in Creatures |-> state[c].mcount], Creatures) = 2 * M

TypeOKInv == TypeOK

====