---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Color definitions
\* ----------------------------------------------------------------------
ColorMinusFaded == {"blue", "red", "yellow"}
Color == ColorMinusFaded \cup {Faded}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in ColorMinusFaded :
      c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES colors, mall, total

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ colors \in [1..N -> [color : ColorMinusFaded, count : Nat]]
  /\ \A i \in 1..N : colors[i].count = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
       /\ colors[i].color # Faded
       /\ mall' = i
       /\ total' = total
       /\ UNCHANGED colors

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
       /\ colors[i].color # Faded
       /\ colors' = [colors EXCEPT ![i].color = Faded]
       /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall \in 1..N
  /\ total < M
  /\ \E i \in 1..N :
       /\ i # mall
       /\ colors[i].color # Faded
       /\ colors[mall].color # Faded
       /\ LET newcol == Complement(colors[i].color, colors[mall].color) IN
            /\ colors' = [colors EXCEPT
                           ![i]    = [color |-> newcol,
                                      count |-> colors[i].count + 1],
                           ![mall] = [color |-> newcol,
                                      count |-> colors[mall].count + 1]]
            /\ total' = total + 1
            /\ mall' = MeetingPlaceEmpty

Next == \/ Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ colors \in [1..N -> [color : Color, count : Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat
  /\ total <= M

SumMet ==
  total = M => Sum({ colors[i].count : i \in 1..N }) = 2 * M

====