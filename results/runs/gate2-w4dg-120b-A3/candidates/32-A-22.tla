---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of creatures; M: max total meetings; Faded: sentinel color; MeetingPlaceEmpty: sentinel place occupant

Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE IN x[2] + SumOf(S \ {x})

TypeOK ==
    /\ \A c \in Creatures : CHOOSE x \in [c \in Creatures |-> TRUE] : TRUE \in {"blue", "red", "yellow", Faded}
    /\ \A c \in Creatures : CHOOSE x \in [c \in Creatures |-> TRUE] : TRUE \in 0..M
    /\ MeetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ GlobalTotal \in 0..M

\* The complement rule described in the specification: same color -> unchanged;
\* different colors -> both become the third (neither creature's) color.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET colors == {"blue", "red", "yellow"}
         IN CHOOSE x \in colors : x # c1 /\ x # c2

Init ==
    /\ \E f \in [Creatures -> Colors \ {{Faded}}] :
        \E g \in [Creatures -> 0..M] :
            CreatureState = f \cup g
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ GlobalTotal = 0

Enter(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ GlobalTotal < M
    /\ CreatureState[c][1] # Faded
    /\ MeetingPlace' = c
    /\ UNCHANGED <<CreatureState, GlobalTotal>>

Fade(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ GlobalTotal = M
    /\ CreatureState[c][1] # Faded
    /\ CreatureState' = [CreatureState EXCEPT ![c][1] = Faded]
    /\ UNCHANGED <<MeetingPlace, GlobalTotal>>

Meet(c) ==
    /\ MeetingPlace # MeetingPlaceEmpty
    /\ MeetingPlace # c
    /\ CreatureState[c][1] # Faded
    /\ CreatureState[MeetingPlace][1] # Faded
    /\ CreatureState' = [CreatureState EXCEPT ![MeetingPlace] = [Complement(CreatureState[MeetingPlace][1], CreatureState[c][1]), CreatureState[MeetingPlace][2] + 1],
                                   ![c] = [Complement(CreatureState[MeetingPlace][1], CreatureState[c][1]), CreatureState[c][2] + 1]]
    /\ GlobalTotal' = GlobalTotal + 1
    /\ MeetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_<<CreatureState, MeetingPlace, GlobalTotal>>

SumMet == GlobalTotal = M => SumOf(CreatureState) = 2 * M
====