---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be bound in the .cfg file)
\* N  : number of creatures (positive natural)
\* M  : total meetings limit (positive natural)
\* Faded : the special faded state for a creature's color
\* MeetingPlaceEmpty : the special value indicating the meeting place is empty
\* ----------------------------------------------------------------------
CONSTANT N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* Creatures are identified by numbers 1..N
\* Colors are the three primary colors plus the faded state
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors    == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* State variables
\* colorsAndCount : mapping each creature to a pair [color, count]
\* place          : either MeetingPlaceEmpty or the id of a waiting creature
\* totalMeetings  : number of meetings that have occurred so far
\* ----------------------------------------------------------------------
VARIABLES colorsAndCount, place, totalMeetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* Complement function implements the color complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE c1 = "blue"  /\ c2 = "red"    -> "yellow"
    [] c1 = "red"   /\ c2 = "blue"   -> "yellow"
    [] c1 = "blue"  /\ c2 = "yellow" -> "red"
    [] c1 = "yellow"/\ c2 = "blue"   -> "red"
    [] c1 = "red"   /\ c2 = "yellow"-> "blue"
    [] c1 = "yellow"/\ c2 = "red"   -> "blue"
    [] OTHER -> "blue" \* default (should never be reached)

\* ----------------------------------------------------------------------
\* Initial state
\* Each creature gets an arbitrary non‑faded color and a count of 0.
\* The meeting place is empty and no meetings have occurred.
\* ----------------------------------------------------------------------
Init ==
  /\ colorsAndCount \in [Creatures -> [color : Colors \ {Faded},
                                   count : Nat]]
  /\ \A i \in Creatures:
        colorsAndCount[i].color \in {"blue", "red", "yellow"}
        /\ colorsAndCount[i].count = 0
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* 1. Enter empty meeting place
\* 2. Fade out when limit reached
\* 3. Meet and mutate
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colorsAndCount[i].color # Faded
  /\ place' = i
  /\ UNCHANGED << colorsAndCount, totalMeetings >>

FadeOut(i) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ colorsAndCount[i].color # Faded
  /\ colorsAndCount' = [colorsAndCount EXCEPT ![i].color = Faded]
  /\ UNCHANGED << place, totalMeetings >>

MeetAndMutate(i) ==
  /\ place # MeetingPlaceEmpty
  /\ i # place
  /\ colorsAndCount[i].color # Faded
  /\ colorsAndCount[place].color # Faded
  /\ LET newColor == Complement(colorsAndCount[i].color,
                                colorsAndCount[place].color) IN
     /\ colorsAndCount' = [colorsAndCount EXCEPT
         ![i].color   = newColor,
         ![i].count   = @ + 1,
         ![place].color = newColor,
         ![place].count = @ + 1]
  /\ place' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation
\* Any creature may attempt any of the three actions
\* ----------------------------------------------------------------------
Next ==
  \/ \E i \in Creatures: Enter(i)
  \/ \E i \in Creatures: FadeOut(i)
  \/ \E i \in Creatures: MeetAndMutate(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colorsAndCount, place, totalMeetings>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (ensures variables stay within expected domains)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ colorsAndCount \in [Creatures -> [color : Colors,
                                       count : Nat]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat
  /\ totalMeetings <= M

\* ----------------------------------------------------------------------
\* Safety invariant: when the global meeting counter reaches M,
\* the sum of all individual meeting counts equals 2*M.
\* ----------------------------------------------------------------------
SumMet ==
  (totalMeetings = M) =>
    ( \A i \in Creatures: colorsAndCount[i].color = Faded ) \/ 
    ( Sum({ colorsAndCount[i].count : i \in Creatures }) = 2 * M )

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ SumMet

=============================================================================