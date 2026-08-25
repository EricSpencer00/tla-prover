---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Set of creature identifiers
Creatures == 1..N

\* Primary colors
Colors == {"blue", "red", "yellow"}

AllColors == Colors \cup {Faded}

\* Complement rule for two colors
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE col \in Colors : /\ col # c1 /\ col # c2

VARIABLES state, meetingPlace, totalMeetings

\* ----------------------------------------------------------------------
\* Helper: sum over a finite set using FoldSet
\* ----------------------------------------------------------------------
Sum(S, f) ==
  FoldSet(S, 0, LAMBDA x, acc : acc + f[x])

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> [color : AllColors, meetCount : Nat]]
  /\ meetingPlace \in {MeetingPlaceEmpty} \cup Creatures
  /\ totalMeetings \in Nat
  /\ totalMeetings <= M

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in Colors : TRUE,
                                 meetCount |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in Creatures :
       /\ state[c].color # Faded
       /\ meetingPlace' = c
       /\ UNCHANGED <<state, totalMeetings>>

FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E c \in Creatures :
       /\ state[c].color # Faded
       /\ state' = [state EXCEPT ![c].color = Faded]
       /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet ==
  LET w == meetingPlace IN
    /\ w # MeetingPlaceEmpty
    /\ \E c \in Creatures :
         /\ c # w
         /\ state[c].color # Faded
         /\ state[w].color # Faded
         /\ totalMeetings < M
         /\ LET newCol == Complement(state[c].color, state[w].color) IN
              /\ state' = [state EXCEPT
                           ![c] = [color |-> newCol,
                                   meetCount |-> @.meetCount + 1],
                           ![w] = [color |-> newCol,
                                   meetCount |-> @.meetCount + 1]]
              /\ meetingPlace' = MeetingPlaceEmpty
              /\ totalMeetings' = totalMeetings + 1
              /\ UNCHANGED <<>>

Next == Enter \/ FadeOut \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, meetingPlace, totalMeetings>>

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts when all meetings done
\* ----------------------------------------------------------------------
SumMet ==
  totalMeetings = M =>
    Sum(Creatures, LAMBDA c : state[c].meetCount) = 2 * M

====