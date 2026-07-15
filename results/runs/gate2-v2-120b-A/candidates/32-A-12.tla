---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N        \* number of creatures (positive natural)
CONSTANT M        \* total meetings limit (positive natural)
CONSTANT Faded    \* value representing the faded color
CONSTANT MeetingPlaceEmpty \* sentinel for an empty meeting place

\* ----------------------------------------------------------------------
\* Enumerated set of possible colors (including the faded value)
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* Creatures identifiers
\* ----------------------------------------------------------------------
Creatures == 1 .. N

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
CreatureInfo == [color : Colors,
                  met   : Nat]

CreatureMap == [c \in Creatures |-> CreatureInfo]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    cmap,   \* mapping from each creature to its info
    mall,   \* occupant of the meeting place (or MeetingPlaceEmpty)
    total   \* global number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule: given two distinct non‑faded colors, return the third.
\* If the colors are the same, the result is that same color.
Comp(col1, col2) ==
  IF col1 = col2 THEN col1
  ELSE
    CASE col1 = "blue"  /\ col2 = "red"    -> "yellow"
    []  col1 = "red"   /\ col2 = "blue"   -> "yellow"
    []  col1 = "blue"  /\ col2 = "yellow"-> "red"
    []  col1 = "yellow"/\ col2 = "blue"   -> "red"
    []  col1 = "red"   /\ col2 = "yellow"-> "blue"
    []  col1 = "yellow"/\ col2 = "red"   -> "blue"
    []  OTHER -> Faded \* should never happen for valid inputs

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ cmap = [c \in Creatures |-> [color |-> Choose({"blue","red","yellow"}),
                                 met   |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. A non‑faded creature enters an empty meeting place while total < M
Enter(c) ==
  /\ c \in Creatures
  /\ cmap[c].color # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ mall' = c
  /\ UNCHANGED <<cmap, total>>

\* 2. Fade out when the limit has been reached and the place is empty
FadeOut(c) ==
  /\ c \in Creatures
  /\ cmap[c].color # Faded
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ cmap' = [cmap EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, total>>

\* 3. Meet and mutate when the place is occupied by a different creature
Meet(c) ==
  /\ c \in Creatures
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ cmap[c].color # Faded
  /\ cmap[mall].color # Faded
  /\ LET w == mall IN
        /\ cmap' = [cmap EXCEPT
                     ![c].color = Comp(cmap[c].color, cmap[w].color),
                     ![c].met   = @ + 1,
                     ![w].color = @,
                     ![w].met   = @ + 1]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total + 1

\* 4. Stutter (no‑op) to keep the model from deadlocking
Stutter ==
  UNCHANGED <<cmap, mall, total>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<cmap, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (required name: TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ cmap \in CreatureMap
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant reflecting the total‑meetings count (required name: SumMet)
\* ----------------------------------------------------------------------
SumMet ==
  total >= M => 
    ( \A c \in Creatures : cmap[c].met = M ) /\  
    ( \A c \in Creatures : cmap[c].color = Faded )

\* ----------------------------------------------------------------------
\* The module exports the required identifiers
\* ----------------------------------------------------------------------
====