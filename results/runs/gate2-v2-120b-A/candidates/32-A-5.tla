---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,               \* number of creatures (>= 1)
    M,               \* total meetings limit (>= 1)
    Faded,           \* the faded color (a distinct identifier)
    MeetingPlaceEmpty \* the sentinel representing an empty meeting place

\* Colors used in the system
Colors == {"blue", "red", "yellow"}

\* All possible creature identifiers
Creatures == 1 .. N

\* The set of all valid colors a creature may hold
ValidColors == Colors \cup {Faded}

\* State variables
VARIABLES
    state,           \* mapping from a creature to [color |-> c, count |-> n]
    waiting,         \* either MeetingPlaceEmpty or a creature identifier
    total            \* total number of completed meetings

\* A helper record constructor for a creature
CreatureRec(c, n) == [color |-> c, count |-> n]

\* Initialization
Init ==
    /\ state = [i \in Creatures |-> CreatureRec(
            CHOOSE c \in Colors : TRUE,   \* nondeterministically pick a color
            0)]                           \* initial meeting count is 0
    /\ waiting = MeetingPlaceEmpty
    /\ total = 0

\* Complement (mutation) rule
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in Colors : c # c1 /\ c # c2

\* Action: a non‑faded creature enters an empty meeting place
EnterEmpty ==
    /\ waiting = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in Creatures :
        /\ state[i].color # Faded
        /\ waiting' = i
        /\ UNCHANGED <<state, total>>

\* Action: a non‑faded creature fades out when the limit has been reached
FadeOut ==
    /\ waiting = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in Creatures :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ waiting' = MeetingPlaceEmpty
        /\ UNCHANGED total

\* Action: two different creatures meet and both mutate
MeetAndMutate ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting \in Creatures
    /\ \E i \in Creatures :
        /\ i # waiting
        /\ state[i].color # Faded
        /\ state[waiting].color # Faded
        /\ LET newCol == Complement(state[i].color, state[waiting].color) IN
           /\ state' = [state EXCEPT
                ![i].color = newCol,
                ![i].count = @ + 1,
                ![waiting].color = newCol,
                ![waiting].count = @ + 1]
        /\ total' = total + 1
        /\ waiting' = MeetingPlaceEmpty

\* Stuttering step to avoid deadlock when the system is finished
Stutter ==
    /\ waiting = MeetingPlaceEmpty
    /\ total >= M
    /\ UNCHANGED <<state, waiting, total>>

\* The overall next-state relation
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Stutter

\* Specification
Spec ==
    Init /\ [][Next]_<<state, waiting, total>>

\* Type correctness invariant
TypeOK ==
    /\ state \in [Creatures -> [color : ValidColors, count : Nat]]
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

\* Safety invariant: when the meeting limit is reached, the sum of individual
\* meeting counts equals twice the number of completed meetings.
SumMet ==
    total = M => 
        ( \A i \in Creatures : state[i].count <= M ) /\ 
        ( \E sum == 2 * M :
            sum = \Sum i \in Creatures : state[i].count )

\* The set of invariants that the .cfg file will refer to
Inv == /\ TypeOK /\ SumMet

\* Liveness property (not required by the .cfg, but provided for completeness)
Termination ==
    []<>(total = M /\ waiting = MeetingPlaceEmpty)

====