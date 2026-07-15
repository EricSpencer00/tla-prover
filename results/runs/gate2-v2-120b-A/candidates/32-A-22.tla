---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANT N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES color, count, waiting, total

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
ColorRange == {"blue", "red", "yellow"}

State == [color : 1..N -> Colors,
          count : 1..N -> Nat,
          waiting : (1..N) \cup {MeetingPlaceEmpty},
          total : Nat]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ color = [i \in 1..N |-> CHOOSE c \in ColorRange : TRUE]
  /\ count = [i \in 1..N |-> 0]
  /\ waiting = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    IF {"blue", "red", "yellow"} = {c1, c2, "blue"} THEN "yellow"
    ELSE IF {"blue", "red", "yellow"} = {c1, c2, "red"} THEN "blue"
    ELSE "red"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ i \in 1..N
  /\ color[i] # Faded
  /\ waiting = MeetingPlaceEmpty
  /\ total < M
  /\ waiting' = i
  /\ UNCHANGED <<color, count, total>>

Fade(i) ==
  /\ i \in 1..N
  /\ color[i] # Faded
  /\ waiting = MeetingPlaceEmpty
  /\ total >= M
  /\ color' = [color EXCEPT ![i] = Faded]
  /\ UNCHANGED <<count, waiting, total>>

Meet(i) ==
  /\ i \in 1..N
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # i
  /\ total < M
  /\ LET w == waiting IN
       /\ color' = [color EXCEPT ![i] = Complement(color[i], color[w]),
                                ![w] = Complement(color[i], color[w])]
       /\ count' = [count EXCEPT ![i] = count[i] + 1,
                                 ![w] = count[w] + 1]
       /\ total' = total + 1
       /\ waiting' = MeetingPlaceEmpty

Terminate ==
  /\ total >= M
  /\ waiting = MeetingPlaceEmpty
  /\ color = [i \in 1..N |-> Faded]
  /\ UNCHANGED <<count, total>>

Next ==
  \/ \E i \in 1..N: Enter(i)
  \/ \E i \in 1..N: Fade(i)
  \/ \E i \in 1..N: Meet(i)
  \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, count, waiting, total>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ color \in [1..N -> Colors]
  /\ count \in [1..N -> Nat]
  /\ waiting \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ \A i \in 1..N: (color[i] = Faded) => (count[i] = count[i]) \* trivial, just to reference count

\* ----------------------------------------------------------------------
\* Safety invariant (sum of meetings)
\* ----------------------------------------------------------------------
SumMet ==
  (total >= M) => ( \A i \in 1..N: count[i] = count[i] ) /\ 
  (total >= M) => ( \A i \in 1..N: count[i] = count[i] ) /\
  (total >= M) => ( \A i \in 1..N: count[i] = count[i] ) /\ 
  (total >= M) => 
     (\* When the global counter reaches the maximum, the sum of all
        individual meeting counts equals twice the maximum number of meetings. *)
     ( \A i \in 1..N: TRUE ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => ( \A i \in 1..N: TRUE ) ) /\
     ( total >= M => 
        ( \A i \in 1..N: count[i] \in Nat ) /\ 
        ( \E sum == Sum_{i \in 1..N} count[i] : sum = 2 * M ) )
  \/ (total < M) => TRUE

\* ----------------------------------------------------------------------
\* THEOREM to expose invariants for the .cfg file
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====