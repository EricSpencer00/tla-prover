---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

\* Creature identifiers are 1, 2, 3, and so on.
Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
Occupiable == Creatures \cup {MeetingPlaceEmpty}

VARIABLES state, meetingPlace, totalMeetings

vars == <<state, meetingPlace, totalMeetings>>

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, metBy: 0 .. M]]
    /\ meetingPlace \in Occupiable
    /\ totalMeetings \in 0 .. M

Init ==
    /\ state \in [Creatures -> [color: {"blue", "red", "yellow"}, metBy: 0 .. M]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* The complement rule: two unlike colors yield the third color in the set.
MutualComplement ==
    LET colors == {"blue", "red", "yellow"}
        third(c1, c2) ==
            IF c1 = c2 THEN c1
            ELSE CHOOSE c \in colors : c # c1 /\ c # c2
    IN [c1 \in colors, c2 \in colors |-> third(c1, c2)]

EnterPlace(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ state[c].color # Faded
    /\ state' = [state EXCEPT ![c] = [color |-> Faded, metBy |-> state[c].metBy]]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* A meeting is always between two distinct, non-faded creatures.
MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ state[c].color # Faded
    /\ state[meetingPlace].color # Faded
    /\ totalMeetings < M
    /\ LET mc == MutualComplement
           nc == mc[c, meetingPlace]
       IN /\ state' = [state EXCEPT ![c] = [color |-> nc, metBy |-> state[c].metBy + 1],
                                   ![meetingPlace] = [color |-> nc,
                                                       metBy |-> state[meetingPlace].metBy + 1]]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* The global meeting total is exactly half the sum of individual meeting counts,
\* which can only hold if every meeting involved two participants and nothing else.
SumMet ==
    totalMeetings * 2 = LET f[S \in SUBSET Creatures] ==
                            IF S = {} THEN 0
                            ELSE LET x == CHOOSE y \in S : TRUE
                                 IN state[x].metBy + f[S \ {x}]
                         IN f[Creatures]

\* Bounded capacity: no meeting occurs once the meeting counter is spent.
Exhausted == totalMeetings = M

\* Once the meeting counter is spent, every creature that is not already faded
\* eventually becomes faded, so the system always reaches a fully faded state.
FadesOut == \A c \in Creatures : (state[c].color # Faded) ~> (state[c].color = Faded)

====