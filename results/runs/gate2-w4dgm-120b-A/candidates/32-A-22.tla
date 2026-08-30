---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature carries its color and how many meetings it has taken part in.
CREATURE == 0..(N - 1)
COLORS == {"blue", "red", "yellow", Faded}
\* The complement rule: given two colors, return the pair of new colors.
Complement(c1, c2) ==
    IF c1 = c2 THEN <<c1, c2>>
    ELSE LET s == {"blue", "red", "yellow"} \ {c1, c2} IN <<CHOOSE c \in s : TRUE, CHOOSE c \in s : TRUE>>

VARIABLES mesh, occupant, meetings

vars == <<mesh, occupant, meetings>>

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN mesh[x][2] + SumOf(S \ {x})

TypeOK ==
    /\ mesh \in [CREATURE -> [color: COLORS, meetings: 0..M]]
    /\ occupant \in CREATURE \cup {MeetingPlaceEmpty}
    /\ meetings \in 0..M

Init ==
    /\ mesh \in [CREATURE -> [color: {"blue", "red", "yellow"}, meetings: 0]]
    /\ occupant = MeetingPlaceEmpty
    /\ meetings = 0

EnterPlace ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetings < M
    /\ \E c \in CREATURE :
         /\ mesh[c].color # Faded
         /\ occupant' = c
    /\ UNCHANGED <<mesh, meetings>>

\* When the place has closed, a creature that tries to enter simply fades out.
FadeOut ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetings = M
    /\ \E c \in CREATURE :
         /\ mesh[c].color # Faded
         /\ mesh' = [mesh EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<occupant, meetings>>

MeetAndMutate ==
    /\ occupant # MeetingPlaceEmpty
    /\ \E c2 \in CREATURE :
         /\ c2 # occupant
         /\ mesh[occupant].color # Faded
         /\ mesh[c2].color # Faded
         /\ LET p == Complement(mesh[occupant].color, mesh[c2].color)
                a == mesh[occupant][2]
                b == mesh[c2][2]
            IN mesh' = [mesh EXCEPT ![occupant] = [color |-> p[1], meetings |-> a + 1],
                                    ![c2] = [color |-> p[2], meetings |-> b + 1]]
    /\ occupant' = MeetingPlaceEmpty
    /\ meetings' = meetings + 1

Next == EnterPlace \/ FadeOut \/ MeetAndMutate

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(MeetAndMutate)

\* Every meeting accounts for exactly two participant increments.
SumMet == (meetings = M) => (SumOf(CREATURE) = 2 * M)

====