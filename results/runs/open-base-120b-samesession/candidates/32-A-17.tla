---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty, Blue, Red, Yellow

\* ----------------------------------------------------------------------
\* Color set (non‑faded colors)
\* ----------------------------------------------------------------------
Colors == {Blue, Red, Yellow}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES state, place, total

vars == <<state, place, total>>

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state \in [1..N -> [color : Colors \cup {Faded},
                        count : Nat]]
  /\ \A i \in 1..N :
        /\ state[i].color \in Colors
        /\ state[i].count = 0
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ place' = i
        /\ UNCHANGED <<state, total>>

FadeOut ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
  /\ place # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # place
        /\ state[i].color # Faded
        /\ state[place].color # Faded
        /\ LET newc == Complement(state[i].color, state[place].color) IN
            /\ state' = [state EXCEPT
                  ![i]      = [color |-> newc, count |-> @.count + 1],
                  ![place]  = [color |-> newc, count |-> @.count + 1]]
            /\ total' = total + 1
            /\ place' = MeetingPlaceEmpty

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [color : Colors \cup {Faded},
                        count : Nat]]
  /\ place \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  total = M => (Sum(i \in 1..N : state[i].count) = 2 * M)

====