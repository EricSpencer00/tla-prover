---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* There are N creatures (chameneos) that share one meeting place (the "mall").
\* Each creature holds a color drawn from three possibilities, plus a distinguished
\* faded color it takes on only once it tries to enter the mall after the meeting
\* budget is spent. The meeting counter is global: it counts completed meetings
\* across the whole system and gates whether entry is still possible.
\* The complement rule mutates both participants in lockstep.

Creatures == 1..N
Colors == {1, 2, 3}

VARIABLES state, mall, totalMet

vars == <<state, mall, totalMet>>

\* The third color not present -- the rule's complement operation.
Third(i, j) ==
    LET ss == {i, j} IN
    CHOOSE k \in Colors : ss \notin i \cup j /\ k \notin ss

TypeOK ==
    /\ state \in [Creatures -> [color : {1, 2, 3} \cup {Faded}, met : 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

SumMet ==
    LET add[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x].met + add[S \ {x}]
    IN totalMet = M => add[Creatures] = 2 * M

Init ==
    /\ state = [c \in Creatures |->
                    [color |-> (IF c = 1 THEN 1 ELSE (IF c = 2 THEN 2 ELSE 3)), met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

\* A non-faded creature enters the empty meeting place while meetings remain.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMet < M
    /\ mall' = c
    /\ UNCHANGED <<state, totalMet>>

\* Once the meeting budget is spent, entry attempts fade the creature instead.
Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = M
    /\ state[c].color # Faded
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

\* Two distinct creatures meet: both mutate to the complement of their colors,
\* both record the meeting, the global counter advances, and the place empties.
MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ state[c].color # Faded
    /\ mall # MeetingPlaceEmpty
    /\ state[mall].color # Faded
    /\ LET nc == IF state[c].color = state[mall].color
                 THEN state[c].color
                 ELSE Third(state[c].color, state[mall].color)
       IN state' = [state EXCEPT ![c] = [color |-> nc, met |-> @.met + 1],
                             ![mall] = [color |-> nc, met |-> @.met + 1]]
    /\ totalMet' = totalMet + 1
    /\ mall' = MeetingPlaceEmpty

Next == \E c \in Creatures : Enter(c) \/ Fade(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====