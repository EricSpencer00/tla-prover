---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,            \* number of creatures
    M,            \* total meetings limit
    Faded,        \* the faded color
    MeetingPlaceEmpty

(*-------------------------------------------------------------------*)
(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"
ColorSet == {Blue, Red, Yellow, Faded}

(*-------------------------------------------------------------------*)
(* State variables *)
VARIABLES
    state,   \* [i \in 1..N |-> [color : ColorSet, count : Nat]]
    mall,    \* occupant of the meeting place (either a creature id or MeetingPlaceEmpty)
    total    \* total number of completed meetings

(*-------------------------------------------------------------------*)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE IF {c1, c2} = {Blue, Red} THEN
        Yellow
    ELSE IF {c1, c2} = {Red, Yellow} THEN
        Blue
    ELSE IF {c1, c2} = {Blue, Yellow} THEN
        Red
    ELSE
        Faded   \* should never happen

(*-------------------------------------------------------------------*)
(* Initial state *)
Init ==
    /\ \E cmap \in [1..N -> {Blue, Red, Yellow}] :
          state = [i \in 1..N |-> [color |-> cmap[i], count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(*-------------------------------------------------------------------*)
(* Actions *)

Enter(i) ==
    /\ i \in 1..N
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ state[i].color # Faded
    /\ UNCHANGED state
    /\ UNCHANGED total
    /\ mall' = i

Fade(i) ==
    /\ i \in 1..N
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ state[i].color # Faded
    /\ state' = [state EXCEPT ![i].color = Faded]
    /\ UNCHANGED total
    /\ mall' = MeetingPlaceEmpty

Meet(i) ==
    /\ i \in 1..N
    /\ mall # MeetingPlaceEmpty
    /\ i # mall
    /\ total < M
    /\ state[i].color # Faded
    /\ state[mall].color # Faded
    /\ LET newc == Complement(state[i].color, state[mall].color) IN
         /\ state' = [state EXCEPT
                        ![i] = [color |-> newc, count |-> state[i].count + 1],
                        ![mall] = [color |-> newc, count |-> state[mall].count + 1]]
         /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Fade(i)
    \/ \E i \in 1..N : Meet(i)

(*-------------------------------------------------------------------*)
(* Specification *)
Spec ==
    Init /\ [][Next]_<<state, mall, total>>

(*-------------------------------------------------------------------*)
(* Invariants *)

TypeOK ==
    /\ state \in [1..N -> [color : ColorSet, count : Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

SumMet ==
    (total = M) => (Sum(i \in 1..N : state[i].count) = 2 * M)

(*-------------------------------------------------------------------*)
(* Exported identifiers *)
\* The following names are required by the reference .cfg file
CONSTANT
    N, M, Faded, MeetingPlaceEmpty

SPECIFICATION Spec
INVARIANT TypeOK, SumMet

====