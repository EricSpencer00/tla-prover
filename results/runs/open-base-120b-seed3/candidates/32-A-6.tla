---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Blue   == "Blue"
Red    == "Red"
Yellow == "Yellow"
Colors == {Blue, Red, Yellow}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, meetingPlace, totalMeetings

vars == << state, meetingPlace, totalMeetings >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule: if colors are equal keep them, otherwise pick the third.
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in Colors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [i \in 1..N |-> [color |-> CHOOSE col \in Colors : TRUE,
                              cnt   |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place
\* ----------------------------------------------------------------------
Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in 1..N :
        /\ state[c].color # Faded
        /\ meetingPlace' = c
        /\ UNCHANGED << state, totalMeetings >>
  /\ UNCHANGED meetingPlace

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature tries to enter after limit reached and fades
\* ----------------------------------------------------------------------
FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E c \in 1..N :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED << meetingPlace, totalMeetings >>
  /\ UNCHANGED meetingPlace

\* ----------------------------------------------------------------------
\* Action: two different non‑faded creatures meet and mutate
\* ----------------------------------------------------------------------
MeetAndMutate ==
  /\ meetingPlace = w
  /\ w \in 1..N
  /\ totalMeetings < M
  /\ \E a \in 1..N :
        /\ a # w
        /\ state[a].color # Faded
        /\ state[w].color # Faded
        /\ LET newCol == Complement(state[a].color, state[w].color) IN
             /\ state' = [state EXCEPT
                           ![a].color = newCol,
                           ![a].cnt   = @ + 1,
                           ![w].color = newCol,
                           ![w].cnt   = @ + 1]
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ totalMeetings' = totalMeetings + 1
  /\ UNCHANGED meetingPlace

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ Enter
  \/ FadeOut
  \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [color : Colors \cup {Faded}, cnt : Nat]]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat
  /\ totalMeetings <= M

\* ----------------------------------------------------------------------
\* Sum of meetings invariant (safety property)
\* ----------------------------------------------------------------------
SumMet ==
  (totalMeetings = M) => 
    ( \* total of individual counts equals twice the number of meetings
      ( \A i \in 1..N : state[i].cnt \in Nat ) /\
      ( \E sum \in Nat :
          sum = \Sum i \in 1..N : state[i].cnt
          /\ sum = 2 * M) )

====