---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and helper definitions
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow"} \cup {Faded}
PrimaryColors == {"blue", "red", "yellow"}

\* Complement rule: if same color, keep it; otherwise adopt the third primary color
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in PrimaryColors : /\ c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mp, total

\* state[c] = [col |-> color, cnt |-> meetingCount]
\* mp = MeetingPlaceEmpty or a creature identifier (in 1..N)
\* total = total number of completed meetings
\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ mp = MeetingPlaceEmpty
  /\ total = 0
  /\ \A c \in 1..N:
        state[c] = [col |-> CHOOSE col \in PrimaryColors,
                    cnt |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mp = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ state[c].col # Faded
        /\ UNCHANGED state
        /\ mp' = c
        /\ total' = total
        /\ UNCHANGED <<state, total>>

FadeOut ==
  /\ mp = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in 1..N :
        /\ state[c].col # Faded
        /\ state' = [state EXCEPT ![c].col = Faded]
        /\ UNCHANGED <<mp, total>>

Meet ==
  /\ mp # MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in 1..N :
        /\ c # mp
        /\ state[c].col # Faded
        /\ state[mp].col # Faded
        /\ LET newCol == Complement(state[c].col, state[mp].col) IN
           /\ state' = [state EXCEPT
                         ![c].col = newCol,
                         ![c].cnt = @ + 1,
                         ![mp].col = newCol,
                         ![mp].cnt = @ + 1]
        /\ mp' = MeetingPlaceEmpty
        /\ total' = total + 1

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mp, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [col : Colors, cnt : Nat]]
  /\ mp \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

SumMet ==
  (total = M) => (Sum(1..N, LAMBDA c : state[c].cnt) = 2 * M)

====