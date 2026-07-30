---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature (indexed 1..N) carries a color and a personal meeting count.
\* The meeting place holds at most one waiting creature; a meeting mutates
\* both creatures' colors according to a three-color complement rule.
\* When M meetings have occurred the place closes and entrants fade out.

NoColor == "none"

VARIABLES pstate, occupant, total
vars == << pstate, occupant, total >>

Colors == {"blue", "red", "yellow"}

\* The complement rule: with three colors, two different ones map to the third,
\* while two equal ones stay the same.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET S == {a, b} IN CHOOSE c \in Colors : S \cup {c} = Colors

SumOfIndividualCounts ==
  LET g[S \in SUBSET (1..N)] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN pstate[x][2] + g[S \ {x}]
  IN g[1..N]

TypeOK ==
  /\ pstate \in [1..N -> (Colors \cup {Faded}) \X (0..M)]
  /\ occupant \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ \E c \in [1..N -> Colors] : pstate = [i \in 1..N |-> << c[i], 0 >>]
  /\ occupant = MeetingPlaceEmpty
  /\ total = 0

Enter ==
  /\ occupant = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
       /\ pstate[i][1] # Faded
       /\ occupant' = i
  /\ UNCHANGED << pstate, total >>

FadeOut ==
  /\ occupant = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
       /\ pstate[i][1] # Faded
       /\ pstate' = [pstate EXCEPT ![i][1] = Faded]
  /\ UNCHANGED << occupant, total >>

MeetAndMutate ==
  /\ occupant # MeetingPlaceEmpty
  /\ \E j \in 1..N :
       /\ j # occupant
       /\ pstate[j][1] # Faded
       /\ LET c1 == pstate[occupant][1]
              c2 == pstate[j][1]
              newcol == Complement(c1, c2)
          IN pstate' = [pstate EXCEPT
                          ![occupant] = << newcol, @ [2] + 1 >>,
                          ![j] = << newcol, @ [2] + 1 >>]
  /\ total' = total + 1
  /\ occupant' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

SumMet ==
  (total = M) => (SumOfIndividualCounts = 2 * M)

====