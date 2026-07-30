---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* a creature's meeting count can never exceed the global total count, so the
\* bound on the meeting counter also bounds every per-creature counter.
\* (N bound is the number of creatures, not the meeting total, so neither bound
\* is redundant.)
CONSTANTSBound == M + 1

Alias(c) == IF c = "blue" THEN "red"
            ELSE IF c = "red" THEN "yellow"
            ELSE IF c = "yellow" THEN "blue"
            ELSE Faded

\* The complement rule, factored so the two creatures always land on the same
\* new color: the third color if they differ, otherwise the shared one.
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE Alias(c1)

\* The shared meeting place holds at most one creature waiting for a partner.
VARIABLES participant, meetCount, globalCount

vars == <<participant, meetCount, globalCount>>

\* A participant is a pair, so the global invariant below can sum the meeting
\* counts with simple arithmetic over the whole table.
SumOf(b) == LET g[S \in SUBSET (1 .. N)] ==
                IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN b[x] + g[S \ {x}]
           IN g[1 .. N]

TypeOK ==
  /\ participant \in [1 .. N \cup {MeetingPlaceEmpty}]
  /\ meetCount \in [1 .. N -> 0 .. M]
  /\ globalCount \in 0 .. M

Init ==
  /\ \E c \in {"blue", "red", "yellow"} :
       participant = [p \in 1 .. N |-> [color |-> c, count |-> 0]]
  /\ meetCount = [p \in 1 .. N |-> 0]
  /\ globalCount = 0

EnterEmptyPlace(p) ==
  /\ participant' = [participant EXCEPT ![MeetingPlaceEmpty] = p]
  /\ UNCHANGED <<meetCount, globalCount>>

FadeOut(p) ==
  /\ participant[p].color # Faded
  /\ participant' = [participant EXCEPT ![p].color = Faded]
  /\ UNCHANGED <<meetCount, globalCount>>

\* Both creatures share the same new color; both individual counts, and the
\* global count, advance together.
MeetAndMutate(p) ==
  /\ participant[MeetingPlaceEmpty] # MeetingPlaceEmpty
  /\ participant[MeetingPlaceEmpty] # p
  /\ participant[p].color # Faded
  /\ globalCount < M
  /\ LET q == participant[MeetingPlaceEmpty] IN
       /\ let c == Complement(participant[q].color, participant[p].color) in
            /\ participant' = [participant EXCEPT ![q].color = c, ![p].color = c]
       /\ meetCount' = [meetCount EXCEPT ![q] = @ + 1, ![p] = @ + 1]
  /\ globalCount' = globalCount + 1
  /\ participant' = [participant EXCEPT ![MeetingPlaceEmpty] = MeetingPlaceEmpty]

Next ==
  \/ \E p \in 1 .. N : EnterEmptyPlace(p)
  \/ \E p \in 1 .. N : FadeOut(p)
  \/ \E p \in 1 .. N : MeetAndMutate(p)

Spec == Init /\ [][Next]_vars

\* When meetings stop, every creature's individual participation adds up to
\* exactly twice the number of meetings that took place.
SumMet ==
  globalCount = M => SumOf(meetCount) = 2 * M

====