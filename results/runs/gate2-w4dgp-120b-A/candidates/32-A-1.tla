---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES creatureState, waiting, totalMet

vars == <<creatureState, waiting, totalMet>>

Creatures == 1..N
Colors == {Faded} \cup {1, 2, 3}
Complement(c, d) ==
    IF c = d THEN c
    ELSE LET a1 == {1, 2, 3} \ {c, d} IN CHOOSE x \in a1 : TRUE

\* The total number of creature-meeting participations is exactly twice the
\* number of meetings that have occurred, which holds exactly when no
\* meeting is ever lost or invented (each meeting involves two creatures).
SumMet == LET sum(S) == IF S = {} THEN 0
                     ELSE LET x == CHOOSE y \in S : TRUE
                          IN creatureState[x][2] + sum(S \ {x})
              IN sum(Creatures) = 2 * totalMet

TypeOK ==
    /\ creatureState \in [Creatures -> (Colors \X (0..M))]
    /\ waiting \in (Creatures \cup {MeetingPlaceEmpty})
    /\ totalMet \in 0..M

Init ==
    /\ creatureState = [i \in Creatures |-> <<i, 0>>]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMet = 0

EnterEmpty ==
    /\ totalMet < M
    /\ waiting = MeetingPlaceEmpty
    /\ \E i \in Creatures :
         /\ creatureState[i][1] # Faded
         /\ waiting' = i
    /\ UNCHANGED <<creatureState, totalMet>>

FadeOut ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ \E i \in Creatures :
         /\ creatureState[i][1] # Faded
         /\ creatureState' = [creatureState EXCEPT ![i] = <<Faded, @ [2]>>]
    /\ UNCHANGED <<waiting, totalMet>>

MeetAndMutate ==
    /\ waiting # MeetingPlaceEmpty
    /\ \E i \in Creatures :
         /\ creatureState[i][1] # Faded
         /\ i # waiting
         /\ LET newc == Complement(creatureState[i][1], creatureState[waiting][1])
            IN creatureState' = [creatureState EXCEPT ![i] = <<newc, @ [2] + 1>, ![waiting] = <<newc, @ [2] + 1>>]
         /\ waiting' = MeetingPlaceEmpty
    /\ totalMet' = totalMet + 1

Next == EnterEmpty \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

====