---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and its personal meeting count.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET rest == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE x \in rest : TRUE

VARIABLES state, mall, totalMeetings

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ state[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ state[c].color # Faded
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMeetings>>

MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ state[c].color # Faded
    /\ state[mall].color # Faded
    /\ LET newcol == Complement(state[c].color, state[mall].color) IN
        /\ state' = [state EXCEPT ![c].color = newcol, ![c].met = @ + 1,
                                   ![mall].color = newcol, ![mall].met = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

SumMet ==
    LET f[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x].met + f[S \ {x}]
    IN f[Creatures]

\* Every meeting is a two-way handshake, so the global count is half the sum of
\* the per-creature counts; this holds exactly at the meeting ceiling.
SumMet == totalMeetings * 2

====