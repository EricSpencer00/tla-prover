---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
Comps == {"blue", "red", "yellow"}

\* The complement rule: same colors stay, different colours yield the third.
ColorComp(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET r == {c1, c2} \cap Comps IN Comps \ r

VARIABLES w4m, occupant, meetings

vars == <<w4m, occupant, meetings>>

Sum(f) == LET g[S \in SUBSET Creatures] ==
              IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN f[x] + g[S \ {x}]
          IN g[Creatures]

TypeOK ==
    /\ w4m \in [Creatures -> [col : Colors, seen : 0 .. M]]
    /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ meetings \in 0 .. M

Init ==
    /\ w4m = [c \in Creatures |-> [col |-> CHOOSE k \in Comps : TRUE, seen |-> 0]]
    /\ occupant = MeetingPlaceEmpty
    /\ meetings = 0

EnterPlace(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetings < M
    /\ w4m[c].col # Faded
    /\ occupant' = c
    /\ UNCHANGED <<w4m, meetings>>

FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetings = M
    /\ w4m[c].col # Faded
    /\ w4m' = [w4m EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<occupant, meetings>>

\* A meeting touches the waiting creature and the arriving one, never itself.
Meet(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ meetings < M
    /\ LET np1 == ColorComp(w4m[occupant].col, w4m[c].col) IN
         w4m' = [w4m EXCEPT ![occupant] = [col |-> np1,
                                          seen |-> @.seen + 1],
                 ![c] = [col |-> np1, seen |-> @.seen + 1]]
    /\ meetings' = meetings + 1
    /\ occupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterPlace(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting is a pairwise encounter, so the per-creature tallies add up
\* to exactly twice the number of meetings -- and only when meetings are maxed.
SumMet == meetings = M => Sum([c \in Creatures |-> w4m[c].seen]) = 2 * M

====