---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors == {"blue", "red", "yellow"}

\* Helper: the third color not equal to c1 or c2
ThirdColor(c1, c2) ==
    CHOOSE c \in Colors : c # c1 /\ c # c2

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE ThirdColor(c1, c2)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Color, Count, TotalMeetings, MeetingPlace

\* ----------------------------------------------------------------------
\* Type checking invariant (required by the .cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Color \in [Creatures -> {blue, red, yellow, Faded}]
    /\ Count \in [Creatures -> Nat]
    /\ TotalMeetings \in Nat
    /\ MeetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ (MeetingPlace = MeetingPlaceEmpty) \/ 
       (MeetingPlace \in Creatures)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Color \in [Creatures -> {blue, red, yellow}]
    /\ Count = [c \in Creatures |-> 0]
    /\ TotalMeetings = 0
    /\ MeetingPlace = MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings < M
    /\ Color[c] # Faded
    /\ MeetingPlace' = c
    /\ UNCHANGED <<Color, Count, TotalMeetings>>

FadeOut(c) ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings >= M
    /\ Color[c] # Faded
    /\ Color' = [Color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<Count, TotalMeetings, MeetingPlace>>

Meet(c1, c2) ==
    /\ MeetingPlace = c1
    /\ c1 # c2
    /\ Color[c1] # Faded
    /\ Color[c2] # Faded
    /\ MeetingPlace' = MeetingPlaceEmpty
    /\ Color' = [Color EXCEPT
                 ![c1] = Complement(Color[c1], Color[c2]),
                 ![c2] = Complement(Color[c1], Color[c2])]
    /\ Count' = [Count EXCEPT
                 ![c1] = Count[c1] + 1,
                 ![c2] = Count[c2] + 1]
    /\ TotalMeetings' = TotalMeetings + 1

\* Next-state relation (exactly one action occurs)
Next ==
    \E c \in Creatures : EnterEmpty(c) \/
    \E c1 \in Creatures :
        \E c2 \in Creatures \ {c1} : Meet(c1, c2) \/
    \E c \in Creatures : FadeOut(c)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Color, Count, TotalMeetings, MeetingPlace>>

\* ----------------------------------------------------------------------
\* Safety invariant required by the .cfg
\* ----------------------------------------------------------------------
SumMet ==
    (TotalMeetings = M) => 
        (SUM(c \in Creatures) Count[c] = 2 * M)

====