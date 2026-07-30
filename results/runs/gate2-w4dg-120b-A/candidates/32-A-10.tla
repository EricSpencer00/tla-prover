---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1
ASSUME Faded \notin {"blue", "red", "yellow"}
ASSUME MeetingPlaceEmpty \notin 1..N

\* A creature's record: its current color and its per-creature meeting count.
VARIABLES rec, meetingPlace, total

vars == <<rec, meetingPlace, total>>

State == [color : {"blue", "red", "yellow", Faded}, count : 0..M]
FullRec == [c \in 1..N |-> State]

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

TotalRec == SumF([c \in 1..N |-> rec[c].count], 1..N)

Init ==
  /\ rec \in FullRec
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total = 0

\* The meeting place is a single slot: only one creature waits in it at a time.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ rec[c].color # Faded
  /\ total < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<rec, total>>

\* Closure: once the meeting budget is spent, creatures 'fade out' rather than wait.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ rec[c].color # Faded
  /\ total = M
  /\ rec' = [rec EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, total>>

Complement(a, b) ==
  IF rec[a].color = rec[b].color
  THEN rec[a].color
  ELSE IF rec[a].color = "blue" /\ rec[b].color = "red" \/ rec[a].color = "red" /\ rec[b].color = "blue"
       THEN "yellow"
       ELSE IF rec[a].color = "blue" /\ rec[b].color = "yellow" \/ rec[a].color = "yellow" /\ rec[b].color = "blue"
            THEN "red"
            ELSE "blue"

\* A meeting mutates both participants' colors together and draws from the budget.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ rec[c].color # Faded
  /\ rec[meetingPlace].color # Faded
  /\ total < M
  /\ LET newcol == Complement(c, meetingPlace) IN
        /\ rec' = [rec EXCEPT ![c].color = newcol, ![meetingPlace].color = newcol,
                   ![c].count = @ + 1, ![meetingPlace].count = @ + 1]
  /\ total' = total + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \E c \in 1..N : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ rec \in FullRec
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

\* Every meeting is double-counted in the per-creature tallies,
\* so when the budget is spent the two counts must match.
SumMet ==
  (total = M) => (TotalRec = 2 * M)

====