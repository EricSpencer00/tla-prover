---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\*   N  - number of creatures (positive natural)
\*   M  - total number of meetings after which the mall closes (positive natural)
\*   Faded - the special color indicating a creature has faded
\*   MeetingPlaceEmpty - the special value denoting that the meeting place is empty
\* ----------------------------------------------------------------------
CONSTANT N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1..N

\* ----------------------------------------------------------------------
\* Variables
\*   state      : a function mapping each creature to a pair [color, count]
\*   mall       : either MeetingPlaceEmpty or a creature identifier
\*   totalCount : the global number of completed meetings
\* ----------------------------------------------------------------------
VARIABLES state, mall, totalCount

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ColorOf(c) == state[c][1]
CountOf(c) == state[c][2]

\* Complement rule for two distinct colors
Comp(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF {"blue", "red", "yellow"} = {c1, c2, "blue"} THEN "yellow"
  ELSE IF {"blue", "red", "yellow"} = {c1, c2, "red"}  THEN "blue"
  ELSE "red"

\* ----------------------------------------------------------------------
\* Initial predicate
\* Each creature gets a non‑faded color nondeterministically and a count of 0.
\* The mall is empty and no meetings have occurred.
\* ----------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> <<CHOOSE col \in {"blue","red","yellow"} : TRUE , 0>>]
  /\ mall = MeetingPlaceEmpty
  /\ totalCount = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
  /\ totalCount < M
  /\ \E c \in Creatures :
        /\ ColorOf(c) # Faded
        /\ mall = MeetingPlaceEmpty
        /\ mall' = c
        /\ UNCHANGED <<state, totalCount>>

FadeOut ==
  /\ totalCount >= M
  /\ \E c \in Creatures :
        /\ ColorOf(c) # Faded
        /\ mall = MeetingPlaceEmpty
        /\ state' = [state EXCEPT ![c][1] = Faded]
        /\ UNCHANGED <<mall, totalCount>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ \E c \in Creatures :
        /\ c # mall
        /\ ColorOf(c) # Faded
        /\ ColorOf(mall) # Faded
        /\ LET newcol == Comp(ColorOf(c), ColorOf(mall)) IN
           /\ state' = [state EXCEPT
                         ![c][1] = newcol,
                         ![c][2] = state[c][2] + 1,
                         ![mall][1] = newcol,
                         ![mall][2] = state[mall][2] + 1]
           /\ mall' = MeetingPlaceEmpty
           /\ totalCount' = totalCount + 1

\* Stuttering step to avoid deadlock when the system has terminated
Terminate ==
  /\ mall = MeetingPlaceEmpty
  /\ totalCount >= M
  /\ \A c \in Creatures : ColorOf(c) = Faded
  /\ UNCHANGED <<state, mall, totalCount>>

Next == EnterEmpty \/ FadeOut \/ Meet \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, totalCount>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (ensures all variables stay within their domains)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> Seq(2)]
  /\ \A c \in Creatures :
        /\ state[c][1] \in Colors
        /\ state[c][2] \in Nat
  /\ mall \in (Creatures \cup {MeetingPlaceEmpty})
  /\ totalCount \in Nat
  /\ totalCount <= M

\* ----------------------------------------------------------------------
\* Safety invariant: when totalCount reaches the limit, the sum of all
\* individual meeting counts equals twice the total number of meetings.
\* ----------------------------------------------------------------------
SumMet ==
  (totalCount = M) => (/\ totalCount * 2 = \Sum c \in Creatures : CountOf(c))

\* ----------------------------------------------------------------------
\* Theorem linking the specification to its invariants (optional but useful)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====