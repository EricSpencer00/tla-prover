---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and derived constants
\* ----------------------------------------------------------------------
Creatures == 1..N

Blue   == "blue"
Red    == "red"
Yellow == "yellow"

InitColors == {Blue, Red, Yellow}
AllColors  == InitColors \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Color(i) == state[i][1]
Count(i) == state[i][2]

\* Complement rule: if colors are equal keep them, otherwise pick the third
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE col \in InitColors : col # c1 /\ col # c2

\* Sum of all individual meeting counts
SumCounts == 
  \* the sum over a finite set can be expressed with a recursive definition
  LET Add(a, b) == a + b IN
  FoldSet(Add, 0, { Count(i) : i \in Creatures })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state \in [Creatures -> (InitColors \X Nat)]
  /\ \A i \in Creatures: Count(i) = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ Color(i) # Faded
  /\ mall' = i
  /\ UNCHANGED <<state, total>>

Fade(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ Color(i) # Faded
  /\ state' = [state EXCEPT ![i] = <<Faded, Count(i)>>]
  /\ UNCHANGED <<mall, total>>

Meet(i) ==
  LET j == mall IN
    /\ j # MeetingPlaceEmpty
    /\ i # j
    /\ total < M
    /\ Color(i) # Faded
    /\ Color(j) # Faded
    LET newcol == Complement(Color(i), Color(j)) IN
      /\ state' = [state EXCEPT
                     ![i] = <<newcol, Count(i) + 1>>,
                     ![j] = <<newcol, Count(j) + 1>>]
      /\ mall' = MeetingPlaceEmpty
      /\ total' = total + 1

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E i \in Creatures: Enter(i)
  \/ \E i \in Creatures: Fade(i)
  \/ \E i \in Creatures: Meet(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> (AllColors \X Nat)]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: when the global counter reaches the limit,
\* the sum of individual counts equals twice the limit.
\* ----------------------------------------------------------------------
SumMet == (total = M) => (SumCounts = 2 * M)

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT == TypeOK /\ SumMet

====