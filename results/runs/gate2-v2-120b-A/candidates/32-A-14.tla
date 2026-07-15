---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N          \* number of creatures
CONSTANT M          \* total meetings limit
CONSTANT Faded      \* the special faded colour
CONSTANT MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ColorSet == {"blue", "red", "yellow", Faded}
Creatures == 1..N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

\* state : [Creatures -> [color : ColorSet, meetCount : Nat]]
\* mall  : either MeetingPlaceEmpty or a creature identifier
\* total : Nat, number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule for two distinct colours (the third colour)
ThirdColour(c1, c2) ==
  CASE c1 = c2 -> c1
  [] (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") -> "yellow"
  [] (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") -> "red"
  [] (c1 = "red" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red") -> "blue"
  [] OTHER -> Faded   \* should never happen; default to faded

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                   meetCount |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(c) ==
  /\ state[c].color # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ mall' = c
  /\ state' = state
  /\ total' = total

Fade(c) ==
  /\ state[c].color # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ mall' = MeetingPlaceEmpty
  /\ total' = total

Meet(c) ==
  /\ state[c].color # Faded
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ LET other == mall IN
       /\ state' = [state EXCEPT
                     ![c].color   = ThirdColour(state[c].color, state[other].color),
                     ![c].meetCount = @ + 1,
                     ![other].color   = ThirdColour(state[c].color, state[other].color),
                     ![other].meetCount = @ + 1]
       /\ mall' = MeetingPlaceEmpty
       /\ total' = total + 1

\* Stuttering step to avoid deadlock when no enabled action exists
Stutter ==
  /\ UNCHANGED <<state, mall, total>>

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> [color : ColorSet, meetCount : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M
  /\ \A c \in Creatures :
        IF state[c].color = Faded THEN state[c].meetCount \in Nat
        ELSE state[c].meetCount \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: when total = M, sum of individual meet counts = 2*M
\* ----------------------------------------------------------------------
SumMet ==
  (total = M) => (Sum({ state[c].meetCount : c \in Creatures }) = 2 * M)

\* ----------------------------------------------------------------------
\* THEOREM (optional, can be checked by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []SumMet

====