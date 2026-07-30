---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 1 .. N

VARIABLES warp, occupant, meetings

vars == << warp, occupant, meetings >>

Colors == {"blue", "red", "yellow", Faded}

TypeOK ==
  /\ warp \in [CREATURES -> [color: Colors, played: 0 .. M]]
  /\ occupant \in (CREATURES \cup {MeetingPlaceEmpty})
  /\ meetings \in 0 .. M

RECURSIVE SumPlayed(_)
SumPlayed(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE e \in S : TRUE IN warp[c].played + SumPlayed(S \ {c})

\* When the meeting place has closed, every creature's individual count still
\* adds up to exactly twice the global count (each meeting gave two participants
\* one more count, so the two tallies must agree).
SumMet == meetings = M => SumPlayed(CREATURES) = 2 * meetings

\* The complement rule: a pair keeps its shared color if equal, otherwise they
\* both adopt the third color not present in the pair.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET S == {a, b} IN CHOOSE c \in Colors \ {Faded} : \A x \in S : x \in Colors \ {c}

Init ==
  /\ warp \in [CREATURES -> [color: {"blue", "red", "yellow"}, played: 0]]
  /\ occupant = MeetingPlaceEmpty
  /\ meetings = 0

EnterPlace(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ meetings < M
  /\ warp[c].color # Faded
  /\ occupant' = c
  /\ UNCHANGED << warp, meetings >>

\* Fading only happens once the meeting place has closed.
FadeOut(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ meetings >= M
  /\ warp[c].color # Faded
  /\ warp' = [warp EXCEPT ![c].color = Faded]
  /\ UNCHANGED << occupant, meetings >>

\* Two different creatures meet in the place and both mutate their color.
MeetAndMutate(c) ==
  /\ occupant # MeetingPlaceEmpty
  /\ occupant # c
  /\ warp[occupant].color # Faded
  /\ warp[c].color # Faded
  /\ meetings < M
  /\ LET g == Complement(warp[occupant].color, warp[c].color) IN
       warp' = [warp EXCEPT ![occupant].color = g, ![c].color = g]
  /\ warp' = [warp' EXCEPT ![occupant].played = warp[occupant].played + 1, ![c].played = warp[c].played + 1]
  /\ meetings' = meetings + 1
  /\ occupant' = MeetingPlaceEmpty

Next ==
  \E c \in CREATURES :
    \/ EnterPlace(c)
    \/ FadeOut(c)
    \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====