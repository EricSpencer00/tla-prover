---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0

Creatures == 0 .. N - 1
Colors == {"blue", "red", "yellow", Faded}

VARIABLES creatureStatus, occupant, globalCount

vars == <<creatureStatus, occupant, globalCount>>

\* creatureStatus[c] = <<color, meetingsParticipated>>
\* occupant is the creature waiting in the meeting place, or MeetingPlaceEmpty

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        LET allc == {"blue", "red", "yellow"}
        IN CHOOSE c \in allc : c # c1 /\ c # c2

TypeOK ==
    /\ creatureStatus \in [Creatures -> [color: Colors, count: 0 .. M]]
    /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ globalCount \in 0 .. M

\* Each creature starts with any non-faded color and zero meetings.
Init ==
    /\ \E f \in [Creatures -> Colors \ {Faded}]:
        creatureStatus = [c \in Creatures |-> [color |-> f[c], count |-> 0]]
    /\ occupant = MeetingPlaceEmpty
    /\ globalCount = 0

\* Creatures enter one at a time; the place closes once the meeting budget is spent.
Enter(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ creatureStatus[c].color # Faded
    /\ globalCount < M
    /\ occupant' = c
    /\ UNCHANGED <<creatureStatus, globalCount>>

FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ creatureStatus[c].color # Faded
    /\ globalCount >= M
    /\ creatureStatus' = [creatureStatus EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<occupant, globalCount>>

\* Two distinct creatures at the meeting place both adopt the complement color.
MeetAndMutate(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ creatureStatus[c].color # Faded
    /\ creatureStatus[occupant].color # Faded
    /\ LET newc == Complement(creatureStatus[c].color, creatureStatus[occupant].color)
       IN creatureStatus' = [creatureStatus EXCEPT
                                ![c].color = newc, ![c].count = @ + 1,
                                ![occupant].color = newc, ![occupant].count = @ + 1]
    /\ globalCount' = globalCount + 1
    /\ occupant' = MeetingPlaceEmpty

Next ==
    \E c \in Creatures: Enter(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == globalCount = M => SumOver([c \in Creatures |-> creatureStatus[c].count], Creatures) = 2 * M

====