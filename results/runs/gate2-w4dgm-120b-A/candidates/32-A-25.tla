---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creature == 1 .. N
Color == {"blue", "red", "yellow", Faded}
\* The third color that is neither of the two argument colors, used by the
\* complement rule.
ThirdOf(c1, c2) ==
    IF {c1, c2} = {"red", "blue"} THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
    ELSE "blue"  \* any of the three; they are equal when this branch applies

VARIABLES state, mall, total
vars == <<state, mall, total>>

\* state[c] = <<color, meetings>>: the creature's current color and the number
\* of meetings it has participated in. mall is either empty or names the
\* waiting creature.
TypeOK ==
    /\ state \in [Creature -> Color \X 0 .. M]
    /\ mall \in Creature \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

SumOf(f) == LET g[S \in SUBSET Creature] ==
                 IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE
                      IN f[x] + g[S \ {x}]
             IN g[Creature]

Init ==
    /\ state \in [Creature -> Color \X 0 .. M]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

EnterMall(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ state[c][2] = 0 \/ TRUE
    /\ state[c][1] # Faded
    /\ mall' = c
    /\ UNCHANGED <<state, total>>

\* The meeting place is closed: a creature that tries to enter instead fades
\* out, and meeting counts are unaffected.
FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ state[c][1] # Faded
    /\ state' = [state EXCEPT ![c] = <<Faded, state[c][2]>>]
    /\ UNCHANGED <<mall, total>>

\* Complementary meeting: both participants adopt the same new color derived
\* from theirs, both meeting counts advance, and the mall is emptied.
MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ total < M
    /\ LET p == mall
           nc == IF state[c][1] = state[p][1]
                 THEN state[c][1]
                 ELSE ThirdOf(state[c][1], state[p][1])
       IN state' = [state EXCEPT ![c] = <<nc, state[c][2] + 1>>,
                               ![p] = <<nc, state[p][2] + 1>>]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next == \E c \in Creature :
            EnterMall(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Every finished meeting is accounted for by exactly two participants, so
\* the global count equals half the sum of individual meeting counts.
MeetingCountCoherence ==
    total * 2 = SumOf([c \in Creature |-> state[c][2]])

\* No state is marked as illegal by the type check.
TypeOKProp == TypeOK
====