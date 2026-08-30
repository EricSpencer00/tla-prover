---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES colstate, mall, totalMet

vars == <<colstate, mall, totalMet>>

Occupied == Cardinality({ c \in Creatures : colstate[c].color = Faded })

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN colstate[x].met + SumOver(S \ {x})

TypeOK ==
    /\ colstate \in [Creatures -> [color : Colors, met : 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ colstate \in [Creatures -> [color : {"blue", "red", "yellow"}, met : 0..M]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ colstate[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<colstate, totalMet>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ colstate[c].color # Faded
    /\ colstate' = [colstate EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

\* The complement rule: same color stays, different colors move to the third.
NewColor(x, y) ==
    IF colstate[x].color = colstate[y].color THEN colstate[x].color
    ELSE LET S == {colstate[x].color, colstate[y].color} IN
         CHOOSE z \in {"blue", "red", "yellow"} : z \notin S

Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ colstate[c].color # Faded
    /\ colstate[mall].color # Faded
    /\ colstate' = [colstate EXCEPT ![c].color = NewColor(c, mall), ![c].met = @ + 1,
                                      ![mall].color = NewColor(c, mall), ![mall].met = @ + 1]
    /\ totalMet' = totalMet + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalMet = M) => (SumOver(Creatures) = 2 * M)

====