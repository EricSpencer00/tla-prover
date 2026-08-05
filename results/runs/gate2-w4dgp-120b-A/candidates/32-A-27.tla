---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Third(a, b) == IF a = b THEN a
               ELSE IF ({a, b} = {"blue", "red"}) THEN "yellow"
               ELSE IF ({a, b} = {"red", "yellow"}) THEN "blue"
               ELSE "red"

VARIABLES colorAndMet, occupant, totalMet

Vars == <<colorAndMet, occupant, totalMet>>

MeetingsSum == LET f[S \in SUBSET Creatures] == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN colorAndMet[x][2] + f[S \ {x}]
               IN f[Creatures]

TypeOK ==
    /\ colorAndMet \in [Creatures -> {Colors} \X (0..M)]
    /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ colorAndMet = [c \in Creatures |-> <<CHOOSE col \in Colors : col # Faded, 0>>]
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet = 0

Enter(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet < M
    /\ colorAndMet[c][1] # Faded
    /\ occupant' = c
    /\ UNCHANGED <<colorAndMet, totalMet>>

FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet = M
    /\ colorAndMet[c][1] # Faded
    /\ colorAndMet' = [colorAndMet EXCEPT ![c] = <<Faded, colorAndMet[c][2>>]
    /\ UNCHANGED <<occupant, totalMet>>

MeetAndMutate(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ LET p == occupant IN
       /\ colorAndMet' = [colorAndMet EXCEPT ![c] = <<Third(colorAndMet[c][1], colorAndMet[p][1]), colorAndMet[c][2] + 1>>,
                                 ![p] = <<Third(colorAndMet[c][1], colorAndMet[p][1]), colorAndMet[p][2] + 1>>]
       /\ totalMet' = totalMet + 1
    /\ occupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_Vars

SumMet ==
    (totalMet = M) => (MeetingsSum = 2 * M)

====