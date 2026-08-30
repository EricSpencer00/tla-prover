---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. Their state is a color plus a
\* per-creature meeting count; the meeting place holds at most one waiting
\* creature at a time, and the global counter tracks total meetings.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
OtherColor(c) == CHOOSE x \in Colors : x \notin {c, Faded}
Sum(f) == LET g[S \in SUBSET Creatures] ==
              IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN f[x] + g[S \ {x}]
          IN g[Creatures]

VARIABLES cstate, waiting, met

vars == <<cstate, waiting, met>>

TypeOK ==
    /\ cstate \in [Creatures -> [color: Colors, met: 0..M]]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ met \in 0..M

Init ==
    /\ cstate \in [Creatures -> [color: {"blue", "red", "yellow"}, met: 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ met = 0

EnterEmpty(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ cstate[c].color # Faded
    /\ met < M
    /\ waiting' = c
    /\ UNCHANGED <<cstate, met>>

FadeOut ==
    /\ waiting = MeetingPlaceEmpty
    /\ met = M
    /\ \E c \in Creatures :
         /\ cstate[c].color # Faded
         /\ cstate' = [cstate EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<waiting, met>>

\* The two creatures must be distinct and both non-faded; the complement rule
\* keeps colors equal if equal, else moves both to the third color.
MeetAndMutate(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ cstate[c].color # Faded
    /\ cstate[waiting].color # Faded
    /\ met < M
    /\ LET newcol == IF cstate[c].color = cstate[waiting].color
                    THEN cstate[c].color ELSE OtherColor(cstate[c].color)
       IN cstate' = [cstate EXCEPT ![c] = [color |-> newcol,
                                          met |-> @.met + 1],
                     ![waiting] = [color |-> newcol,
                                   met |-> @.met + 1]]
    /\ met' = met + 1
    /\ waiting' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterEmpty(c)
    \/ FadeOut
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Every meeting advances the global counter and exactly two creature counters,
\* so when the global count reaches the maximum the sum of creature counts is
\* exactly twice that maximum.
SumMet == (met = M) => (Sum([c \in Creatures |-> cstate[c].met]) = 2 * M)

====