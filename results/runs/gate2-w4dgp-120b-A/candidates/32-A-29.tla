---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures (chameneos) meet pairwise at a shared meeting place (the Mall). A meeting
\* only ever happens while the total number of meetings is below the fixed limit M;
\* once the limit is reached the meeting place closes and creatures that try to enter
\* simply fade out. Because every meeting takes exactly two participants, the sum of
\* all individual meeting counts always equals twice the number of meetings that
\* actually occurred.

Creators == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES creatureState, mall, meetingsSoFar

vars == <<creatureState, mall, meetingsSoFar>>

\* The color complement rule: meeting with a differently-colored creature flips
\* both to the third color in the set; meeting a same-colored creature does
\* nothing to the colors.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET s == {c1, c2} IN CHOOSE c \in Colors \ s : TRUE

Reports == [color : Colors, met : 0..M]

TypeOK ==
    /\ creatureState \in [Creators -> Reports]
    /\ mall \in Creators \cup {MeetingPlaceEmpty}
    /\ meetingsSoFar \in 0..M

Init ==
    /\ creatureState = [c \in Creaturers |-> [color |-> "blue", met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ meetingsSoFar = 0

EnterPlace(c) ==
    /\ creatureState[c].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ meetingsSoFar < M
    /\ mall' = c
    /\ UNCHANGED <<creatureState, meetingsSoFar>>

FadeOut(c) ==
    /\ creatureState[c].color # Faded
    /\ meetingsSoFar >= M
    /\ creatureState' = [creatureState EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, meetingsSoFar>>

\* Two different creatures meet; both adopt the complementary color and both
\* count one more meeting. The meeting place is emptied for the next pair.
MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ meetingsSoFar < M
    /\ creatureState' = [creatureState EXCEPT ![c].color = Complement(creatureState[c].color, creatureState[mall].color),
                                             ![c].met = @ + 1,
                                             ![mall].color = Complement(creatureState[c].color, creatureState[mall].color),
                                             ![mall].met = @ + 1]
    /\ meetingsSoFar' = meetingsSoFar + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creaturers : EnterPlace(c)
    \/ \E c \in Creaturers : FadeOut(c)
    \/ \E c \in Creaturers : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* When the meeting place has closed, all individual counts together account for
\* exactly the meetings that happened -- each meeting contributes two participants.
SumMet == meetingsSoFar = M => (creatureState[0].met + creatureState[1].met + creatureState[2].met) = 2 * M
====