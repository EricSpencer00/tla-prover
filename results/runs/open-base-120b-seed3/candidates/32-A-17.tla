---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
CONSTANT Blue, Red, Yellow
Color == {Blue, Red, Yellow, Faded}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

vars == << state, mall, total >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule: if the two colors are the same, keep it;
\* otherwise return the third (non‑faded) color.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in {Blue, Red, Yellow} : c # c1 /\ c # c2

\* Sum of all meeting counts
SumCounts == \Sum i \in 1..N : state[i].cnt

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state \in [1..N -> [color : Color, cnt : Nat]]
  /\ \A i \in 1..N:
        /\ state[i].cnt = 0
        /\ state[i].color \in {Blue, Red, Yellow}
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ state[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED << state, total >>

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED << mall, total >>

Meet(c) ==
  /\ mall = w
  /\ w # c
  /\ total < M
  /\ state[c].color # Faded
  /\ state[w].color # Faded
  /\ LET newCol == Complement(state[c].color, state[w].color) IN
        /\ state' = [state EXCEPT
                      ![c].color = newCol,
                      ![c].cnt   = @ + 1,
                      ![w].color = newCol,
                      ![w].cnt   = @ + 1]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

\* Non‑deterministic choice of which creature acts
Next ==
  \E c \in 1..N :
    \/ Enter(c)
    \/ Fade(c)
    \/ Meet(c)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [color : Color, cnt : Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat

SumMet ==
  (total = M) => (SumCounts = 2 * M)

====