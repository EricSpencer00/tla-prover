---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
ColorOf(c) == IF c = 1 THEN "blue" ELIF c = 2 THEN "red" ELSE "yellow"

VARIABLES state, mall, totalMet

vars == <<state, mall, totalMet>>

RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: 0 .. M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0 .. M

Init ==
    /\ state = [c \in Creatures |-> [color |-> ColorOf(c), met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

Complement(a, b) ==
    IF a = b THEN a
    ELSE LET S == {a, b} IN CHOOSE c \in {"blue", "red", "yellow} : c \notin S

EnterMall ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ \E c \in Creatures :
         /\ state[c].color # Faded
         /\ mall' = c
    /\ UNCHANGED <<state, totalMet>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ \E c \in Creatures :
         /\ state[c].color # Faded
         /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ \E c \in Creatures :
         /\ c # mall
         /\ state[c].color # Faded
         /\ state[mall].color # Faded
         /\ LET newcol == Complement(state[c].color, state[mall].color) IN
              state' = [state EXCEPT ![c] = [color |-> newcol, met |-> @.met + 1],
                                    ![mall] = [color |-> newcol, met |-> @.met + 1]]
         /\ totalMet' = totalMet + 1
         /\ mall' = MeetingPlaceEmpty

Next ==
    \/ EnterMall
    \/ FadeOut
    \/ Meet

Spec == Init /\ [][Next]_vars

SumMet == SumOver([c \in Creatures |-> state[c].met], Creatures)

MeetingConservation == totalMet = M => SumMet = 2 * M

====