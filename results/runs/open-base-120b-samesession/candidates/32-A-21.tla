---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    N,          \* number of creatures
    M,          \* total meetings limit
    Faded,      \* the special faded color
    MeetingPlaceEmpty  \* sentinel for an empty meeting place

\* ----------------------------------------------------------------------
\* Colors that are not faded
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow"}

AllColors == Colors \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    creatures,   \* mapping 1..N -> <<color, meetingCount>>
    mall,        \* either MeetingPlaceEmpty or a creature id
    total        \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ColorOf(c) == c[1]
CountOf(c) == c[2]

\* Complement rule: if same, keep; otherwise adopt the third color
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        LET rest == Colors \ {c1, c2} IN
            CHOOSE x \in rest : TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ \A i \in 1..N:
          /\ ColorOf(creatures[i]) \in Colors
          /\ CountOf(creatures[i]) = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ ColorOf(creatures[i]) # Faded
          /\ mall' = i
          /\ UNCHANGED <<creatures, total>>
    /\ UNCHANGED <<>>  \* no other changes

Fade ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in 1..N :
          /\ ColorOf(creatures[i]) # Faded
          /\ creatures' = [creatures EXCEPT ![i][1] = Faded]
          /\ UNCHANGED <<mall, total>>
    /\ UNCHANGED <<>>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ i # mall
          /\ ColorOf(creatures[i]) # Faded
          /\ LET w == mall IN
                /\ newColor == Complement(ColorOf(creatures[i]), ColorOf(creatures[w]))
                /\ creatures' = 
                     [creatures EXCEPT 
                         ![i] = <<newColor, CountOf(creatures[i]) + 1>>,
                         ![w] = <<newColor, CountOf(creatures[w]) + 1>>]
                /\ mall' = MeetingPlaceEmpty
                /\ total' = total + 1
          /\ UNCHANGED <<>>

Next ==
    \/ Enter
    \/ Fade
    \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ DOMAIN creatures = 1..N
    /\ \A i \in 1..N:
          /\ ColorOf(creatures[i]) \in AllColors
          /\ CountOf(creatures[i]) \in Nat
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    (total = M) => ( /\ \* when the limit is reached, the sum of counts is 2*M
          LET sum == Sum({i \in 1..N : CountOf(creatures[i])}) IN
              sum = 2 * M)

\* ----------------------------------------------------------------------
\* The set of invariants to be checked by TLC
\* ----------------------------------------------------------------------
INVARIANT TypeOK, SumMet

====