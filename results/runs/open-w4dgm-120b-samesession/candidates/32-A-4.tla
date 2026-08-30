---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
Third(c1, c2) == CHOOSE c \in Colors : c # c1 /\ c # c2

VARIABLES cstate, mall, total

vars == <<cstate, mall, total>>

RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN cstate[x][2] + SumCounts(S \ {x})

TypeOK ==
    /\ cstate \in [Creatures -> (Colors \X (0 .. M))]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

Init ==
    /\ cstate \in [Creatures -> (Colors \ {Faded} \X {0})]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

EnterMeetingPlace(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ cstate[c][1] # Faded
    /\ total < M
    /\ mall' = c
    /\ UNCHANGED <<cstate, total>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ cstate[c][1] # Faded
    /\ total = M
    /\ cstate' = [cstate EXCEPT ![c] = <<Faded, cstate[c][2]>>]
    /\ UNCHANGED <<mall, total>>

MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ total < M
    /\ LET other == mall
           col1 == cstate[c][1]
           col2 == cstate[other][1]
           newCol == IF col1 = col2 THEN col1 ELSE Third(col1, col2)
       IN cstate' = [cstate EXCEPT ![c] = <<newCol, cstate[c][2] + 1>>,
                                ![other] = <<newCol, cstate[other][2] + 1>>]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterMeetingPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (total = M) => (SumCounts(Creatures) = 2 * M)

====