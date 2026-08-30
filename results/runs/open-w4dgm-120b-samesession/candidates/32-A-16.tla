---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, mall, totalMet

vars == <<state, mall, totalMet>>

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ state \in [Creatures -> [color \in {"blue", "red", "yellow"}, met: 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

EnterMall(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ state[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<state, totalMet>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ state[c].color # Faded
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ state[c].color # Faded
    /\ state[mall].color # Faded
    /\ state' = [state EXCEPT ![c].color = Complement(state[c].color, state[mall].color),
                              ![c].met = @ + 1,
                              ![mall].color = Complement(state[c].color, state[mall].color),
                              ![mall].met = @ + 1]
    /\ totalMet' = totalMet + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures: EnterMall(c)
    \/ \E c \in Creatures: FadeOut(c)
    \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

Complement(col1, col2) ==
    IF col1 = col2 THEN col1
    ELSE CHOOSE col \in {"blue", "red", "yellow"} :
            /\ col # col1
            /\ col # col2

SumOfMet ==
    LET g[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN state[x].met + g[S \ {x}]
    IN g[Creatures]

MeetingConservation ==
    totalMet = M => SumOfMet = 2 * M

====