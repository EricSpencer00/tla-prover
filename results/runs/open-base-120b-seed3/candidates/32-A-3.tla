---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the faded colour
    MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colours
\* ----------------------------------------------------------------------
CONSTANTS Blue, Red, Yellow
ColourSet == {Blue, Red, Yellow, Faded}
BaseColours == {Blue, Red, Yellow}

\* Complement rule: if colours equal keep them, otherwise switch to the third colour
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in BaseColours :
            /\ c # c1
            /\ c # c2

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    cstate,   \* [1..N -> [color : ColourSet, cnt : Nat]]
    mall,     \* either MeetingPlaceEmpty or a creature id in 1..N
    total     \* total number of completed meetings

vars == <<cstate, mall, total>>

\* ----------------------------------------------------------------------
\* Initialisation
\* ----------------------------------------------------------------------
Init ==
    /\ cstate \in [1..N -> [color : ColourSet, cnt : Nat]]
    /\ \A i \in 1..N :
          /\ cstate[i].color \in BaseColours
          /\ cstate[i].cnt = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ cstate[i].color # Faded
          /\ mall' = i
          /\ UNCHANGED <<cstate, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in 1..N :
          /\ cstate[i].color # Faded
          /\ cstate' = [cstate EXCEPT ![i].color = Faded]
          /\ UNCHANGED <<mall, total>>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ i # mall
          /\ cstate[i].color # Faded
          /\ cstate[mall].color # Faded
          LET newcol == Complement(cstate[i].color, cstate[mall].color) IN
              /\ cstate' = [cstate EXCEPT
                               ![i].color = newcol,
                               ![i].cnt   = @ + 1,
                               ![mall].color = newcol,
                               ![mall].cnt   = @ + 1]
              /\ total' = total + 1
              /\ mall' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ cstate \in [1..N -> [color : ColourSet, cnt : Nat]]
    /\ \A i \in 1..N :
          /\ cstate[i].color \in ColourSet
          /\ cstate[i].cnt \in Nat
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

SumMet ==
    total = M => ( \* when the limit is reached, the sum of individual counts equals 2*M
        (\* sum over all creatures' cnt fields *)
        (\* TLC's Sum operator works on sequences; we build a sequence of counts *)
        LET cnts == [i \in 1..N |-> cstate[i].cnt] IN
            Sum(Seq(cnts)) = 2 * M
    )

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The constants are declared above.
\* The specification is named Spec.
\* The invariants are TypeOK and SumMet.

====