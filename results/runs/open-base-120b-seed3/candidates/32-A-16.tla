---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty, Blue, Red, Yellow

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Colors == {Blue, Red, Yellow, Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, place, total

\* ----------------------------------------------------------------------
\* Complement rule
\* If the two colors are the same, the result is that color.
\* Otherwise the result is the third color.
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE
      (c1 = Blue  /\ c2 = Red)   \/ (c1 = Red   /\ c2 = Blue)   -> Yellow ;
      (c1 = Blue  /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue)  -> Red ;
      (c1 = Red   /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red)   -> Blue ;
    END

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [i \in 1..N |-> [ color |-> CHOOSE c \in {Blue, Red, Yellow} : TRUE,
                               count |-> 0 ]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place
\* ----------------------------------------------------------------------
Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ place' = i
        /\ UNCHANGED << state, total >>

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature fades when the meeting place is closed
\* ----------------------------------------------------------------------
Fade ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED << place, total >>

\* ----------------------------------------------------------------------
\* Action: two different creatures meet and mutate
\* ----------------------------------------------------------------------
Meet ==
  /\ place \in 1..N               \* there is a waiting creature
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # place
        /\ state[i].color # Faded
        /\ state[place].color # Faded
        /\ LET newc == Complement(state[i].color, state[place].color) IN
              /\ state' = [state EXCEPT
                            ![i].color = newc,
                            ![i].count = @ + 1,
                            ![place].color = newc,
                            ![place].count = @ + 1]
              /\ total' = total + 1
              /\ place' = MeetingPlaceEmpty
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ Enter
  \/ Fade
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, place, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [color : Colors, count : Nat]]
  /\ place \in (MeetingPlaceEmpty) \/ (1..N)
  /\ total \in Nat
  /\ total <= M

\* ----------------------------------------------------------------------
\* Safety invariant: when total meetings reach the limit,
\* the sum of individual meeting counts equals twice the limit
\* ----------------------------------------------------------------------
SumMet ==
  (total = M) => (LET s == Sum({ state[i].count : i \in 1..N }) IN s = 2 * M)

====