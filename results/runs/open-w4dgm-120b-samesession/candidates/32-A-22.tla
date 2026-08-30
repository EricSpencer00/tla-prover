---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a (color, personal-meeting-count) pair; the meeting place is
\* a single waiting slot that can hold at most one creature.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Hall == [Waiting : Creatures \cup {MeetingPlaceEmpty}, Total : 0..M]

VARIABLES state, hall, total

vars == <<state, hall, total>>

RECURSIVE SumOver(_)
SumOver(S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN state[x][2] + SumOver(S \ {x})

TypeOK ==
    /\ state \in [Creatures -> Colors \X 0..M]
    /\ hall \in Hall
    /\ total \in 0..M

Init ==
    /\ state = [c \in Creatures |-> <<CHOOSE k \in Colors : k # Faded, 0>>]
    /\ hall = [Waiting |-> MeetingPlaceEmpty, Total |-> 0]
    /\ total = 0

\* A creature that finds the meeting place closed here simply fades out.
EnterPlace(c) ==
    /\ hall.Waiting = MeetingPlaceEmpty
    /\ total < M
    /\ state[c][1] # Faded
    /\ hall' = [Waiting |-> c, Total |-> hall.Total + 1]
    /\ UNCHANGED <<state, total>>

FadeOut(c) ==
    /\ hall.Waiting = MeetingPlaceEmpty
    /\ total >= M
    /\ state[c][1] # Faded
    /\ state' = [state EXCEPT ![c] = <<Faded, state[c][2>>]
    /\ UNCHANGED <<hall, total>>

\* Two distinct participants meet; both adopt the complement of their pair of
\* colors and record the meeting on their own counters.
Meet(c) ==
    /\ hall.Waiting # MeetingPlaceEmpty
    /\ hall.Waiting # c
    /\ state[c][1] # Faded
    /\ total < M
    /\ LET col1 == state[c][1] col2 == state[hall.Waiting][1]
           nc == IF col1 = col2 THEN col1
                 ELSE CHOOSE k \in Colors :
                          (k # col1 /\ k # col2 /\ k # Faded)
       IN state' = [state EXCEPT ![c] = <<nc, state[c][2] + 1>>,
                    ![hall.Waiting] = <<nc, state[hall.Waiting][2] + 1>>]
    /\ hall' = [Waiting |-> MeetingPlaceEmpty, Total |-> hall.Total + 1]
    /\ total' = total + 1

Next ==
    \/ \E c \in Creatures : EnterPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (total = M) => (SumOver(Creatures) = 2 * M)

====