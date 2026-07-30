---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

\* Chameneos: pairs of creatures meet in a shared meeting place (the Mall) and
\* both mutate their color. Creatures fade out once the total meeting budget is
\* exhausted. The sum of all individual meeting counters must stay in step with
\* the global meeting counter, since every meeting touches exactly two participants.
\* The spec explores every deterministic choice of the complement rule (which is
\* a pure function of the two participants' incoming colors).
CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
ColorTriples == {{c1, c2, c3} \in SUBSET Colors : c1 \notin {c2, c3}}

VARIABLES color, meetingPlace, meetingsTotal

vars == <<color, meetingPlace, meetingsTotal>>

TypeOK ==
  /\ color \in [Creatures -> [col: Colors, seen: 0..(2 * M)]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetingsTotal \in 0..M

SumOver(f, S) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
        IN f[x] + g[T \ {x}]
  IN g[S]

FadedCount ==
  Cardinality({c \in Creatures : color[c].col = Faded})

Init ==
  /\ \E assign \in [Creatures -> Colors \ {{Faded}}]:
       /\ \A c \in Creatures: color[c].col = assign[c]
       /\ \A c \in Creatures: color[c].seen = 0
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = 0

EnterMall(g) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal < M
  /\ color[g].col # Faded
  /\ meetingPlace' = g
  /\ UNCHANGED <<color, meetingsTotal>>

Fade(g) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = M
  /\ color[g].col # Faded
  /\ color' = [color EXCEPT ![g] = [col |-> Faded, seen |-> @.seen]]
  /\ UNCHANGED <<meetingPlace, meetingsTotal>>

Complement(c1, c2) ==
  LET triple == CHOOSE t \in ColorTriples : c1 \in t /\ c2 \in t
  IN CHOOSE x \in triple : x # c1 /\ x # c2

MeetAndMutate(g) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # g
  /\ LET p == meetingPlace
         newcol == Complement(color[p].col, color[g].col)
     IN /\ color' = [color EXCEPT ![p] = [col |-> newcol, seen |-> @.seen + 1],
                              ![g] = [col |-> newcol, seen |-> @.seen + 1]]
  /\ meetingsTotal' = meetingsTotal + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E g \in Creatures: EnterMall(g)
  \/ \E g \in Creatures: Fade(g)
  \/ \E g \in Creatures: MeetAndMutate(g)

Spec == Init /\ [][Next]_vars

SumMet ==
  meetingsTotal = M => SumOver([c \in Creatures |-> color[c].seen], Creatures) = 2 * FadedCount
====