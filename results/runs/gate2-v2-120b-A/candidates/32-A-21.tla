---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,               \* number of creatures
    M,               \* total meeting limit
    Faded,           \* the special faded color
    MeetingPlaceEmpty \* special value indicating empty meeting place

\* --- Derived constants -------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
CreatureIds == 1..N

\* --- State variables ---------------------------------------------------
VARIABLES
    state,          \* [creatureId -> [color : Colors, meetCount : Nat]]
    mall,           \* either MeetingPlaceEmpty or a creatureId
    totalMeetings   \* Nat, total number of completed meetings

\* --- Type definitions --------------------------------------------------
StateRecord == [color : Colors, meetCount : Nat]

\* --- Helper definitions ------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET others == {"blue", "red", "yellow"} \ {c1, c2}
         IN IF Len(others) = 1 THEN CHOOSE x \in others : TRUE
            ELSE Faded \* should never happen

\* --- Initial state -----------------------------------------------------
Init ==
    /\ state = [i \in CreatureIds |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                        meetCount |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* --- Actions -----------------------------------------------------------
\* A non‑faded creature enters an empty mall when the meeting limit is not reached
EnterEmpty ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in CreatureIds :
          /\ state[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED << state, totalMeetings >>

\* When the limit is reached a creature that tries to enter fades out
FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ \E c \in CreatureIds :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED << mall, totalMeetings >>

\* Two different creatures meet and mutate their colors
MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty
    /\ \E c1 \in CreatureIds :
         /\ state[c1].color # Faded
         /\ \E c2 \in CreatureIds :
              /\ c2 # c1
              /\ state[c2].color # Faded
              /\ LET newCol == Complement(state[c1].color, state[c2].color) IN
                 /\ state' = [state EXCEPT
                        ![c1].color = newCol,
                        ![c1].meetCount = @ + 1,
                        ![c2].color = newCol,
                        ![c2].meetCount = @ + 1]
                 /\ totalMeetings' = totalMeetings + 1
                 /\ mall' = MeetingPlaceEmpty

\* Stuttering step to avoid deadlock after termination
Terminate ==
    /\ totalMeetings >= M
    /\ mall = MeetingPlaceEmpty
    /\ UNCHANGED << state, mall, totalMeetings >>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Terminate

\* --- Specification ------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

\* --- Safety invariant: type correctness ---------------------------------
TypeOK ==
    /\ state \in [CreatureIds -> StateRecord]
    /\ mall \in CreatureIds \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

\* --- Safety invariant: sum of individual meeting counts -----------------
SumMet ==
    /\ LET sum == Σ i \in CreatureIds : state[i].meetCount
       IN sum = 2 * totalMeetings

\* The "theorem" below is optional but illustrates that Spec implies the invariants
THEOREM SpecImpliesSafety == Spec => (TypeOK /\ SumMet)

====