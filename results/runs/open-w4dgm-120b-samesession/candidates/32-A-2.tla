---- MODULE Chameneos ----
EXTENDS Naturals

(* A concurrency game modeling symmetrical cooperation among creatures that    *)
(* meet pairwise at a central meeting place.  Each meeting consumes one unit    *)
(* of a bounded budget of meetings: the place is open only while the global    *)
(* meeting counter is below the limit.  After the counter is spent, creatures  *)
(* that try to enter instead fade out.  Safety: when the meeting budget is     *)
(* spent, the sum of individual creatures' meeting counts is exactly twice the *)
(* number of meetings, i.e. every meeting counted two participants.            *)

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
ColorPairs == [Creatures -> [col : Colors, count : 0..(2 * M)]]

\* The complement rule: two same colors stay, two different colors both
\* become the third distinct color.
OTHER(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF c1 = "blue" /\ c2 = "red" THEN "yellow"
    ELSE IF c1 = "blue" /\ c2 = "yellow" THEN "red"
    ELSE IF c1 = "red" /\ c2 = "blue" THEN "yellow"
    ELSE IF c1 = "red" /\ c2 = "yellow" THEN "blue"
    ELSE IF c1 = "yellow" /\ c2 = "blue" THEN "red"
    ELSE "blue"  \* c1 = yellow /\ c2 = red

RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN ColorPairs[x].count + SumCounts(S \ {x})

VARIABLES colorInfo, waiting, totalMet

vars == <<colorInfo, waiting, totalMet>>

TypeOK ==
    /\ colorInfo \in ColorPairs
    /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ colorInfo = [c \in Creatures |-> [col |-> CHOOSE d \in Colors : d # Faded,
                                          count |-> 0]]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMet = 0

EnterEmptyPlace(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ colorInfo[c].col # Faded
    /\ totalMet < M
    /\ waiting' = c
    /\ UNCHANGED <<colorInfo, totalMet>>

FadeOut(c) ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMet = M
    /\ colorInfo[c].col # Faded
    /\ colorInfo' = [colorInfo EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<waiting, totalMet>>

MeetAndMutate(c) ==
    /\ waiting # MeetingPlaceEmpty
    /\ waiting # c
    /\ colorInfo[c].col # Faded
    /\ LET newcol == OTHER(colorInfo[c].col, colorInfo[waiting].col)
       IN  colorInfo' = [colorInfo EXCEPT ![c] = [col |-> newcol,
                                                  count |-> @.count + 1],
                         ![waiting] = [col |-> newcol,
                                       count |-> @.count + 1]]
    /\ waiting' = MeetingPlaceEmpty
    /\ totalMet' = totalMet + 1

Next ==
    \/ \E c \in Creatures : EnterEmptyPlace(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* When the meeting budget is spent, the total count of individual meetings
\* is twice the number of completed meetings: each meeting involved two
\* participants exactly.
SumMet == (totalMet = M) => (SumCounts(Creatures) = 2 * M)

====