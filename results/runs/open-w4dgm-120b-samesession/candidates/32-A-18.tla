---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 1 /\ M \in Nat /\ M >= 1

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, occupant, totalMeetings

vars == <<state, occupant, totalMeetings>>

\* The complement of two colors: the third color of the set {blue, red, yellow}.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET x \in Colors, y \in Colors, z \in Colors :
              /\ x # Faded /\ y # Faded /\ z # Faded
              /\ {c1, c2} = {x, y} /\ z # x /\ z # y
         IN z

Init ==
    /\ \E a \in [Creatures -> Colors \ {Faded}]:
         state = [c \in Creatures |-> <<a[c], 0>>]
    /\ occupant = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ state[c][2] = 0
    /\ state[c][2] < M
    /\ occupant' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ state[c][2] = 0
    /\ totalMeetings >= M
    /\ state' = [state EXCEPT ![c] = <<Faded, 0>>]
    /\ UNCHANGED <<occupant, totalMeetings>>

MeetAndMutate(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ totalMeetings < M
    /\ LET na == Complement(state[c][1], state[occupant][1]) IN
         state' = [state EXCEPT ![c] = <<na, state[c][2] + 1>>,
                              ![occupant] = <<na, state[occupant][2] + 1>>]
    /\ occupant' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creatures: EnterMall(c)
    \/ \E c \in Creatures: FadeOut(c)
    \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ state \in [Creatures -> Colors \X (0 .. M)]
    /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0 .. M

SumMet ==
    (totalMeetings = M) =>
        (2 * M = state[0][2] + state[1][2] + state[2][2]
                     + state[3][2] + state[4][2] + state[5][2])

====