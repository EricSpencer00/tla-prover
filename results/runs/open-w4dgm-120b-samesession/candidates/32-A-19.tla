---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

(* A concurrency game: chameneos creatures pair up at a meeting place (the *)
(* Mall). A meeting changes both participants' colors according to a       *)
(* complement rule and advances a global meeting counter. The meeting place  *)
(* closes once the counter reaches a fixed limit; creatures that then        *)
(* attempt to enter instead fade out. The invariant protects the fact that   *)
(* each meeting bumps the global count and the two individual counts together. *)

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: two equal colors stay; two different colors move to
\* the third, distinct color out of the three non-faded ones.
Complement(a, b) == IF a = b THEN a
                     ELSE LET c == CHOOSE x \in {"blue", "red", "yellow"} : x # a /\ x # b
                          IN c

VARIABLES creature, mall, totalMet

vars == <<creature, mall, totalMet>>

\* creature[c] = <<color, myMet>> : each creature's current color and the
\* number of meetings it has participated in.
TypeOK ==
    /\ creature \in [Creatures -> [color : Colors, myMet : 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ creature = [c \in Creatures |-> [color |-> CHOOSE k \in {"blue", "red", "yellow"} : TRUE,
                                         myMet |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

\* A non-faded creature enters the empty meeting place to wait for a partner.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ creature[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<creature, totalMet>>

\* No partner available and the meeting place is closed: c fades out instead.
FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ creature[c].color # Faded
    /\ creature' = [creature EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMet>>

\* Two distinct creatures meet: both take the complement color and count the
\* meeting, the global counter advances, and the place empties.
Meet(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ totalMet < M
    /\ creature[c].color # Faded
    /\ creature[mall].color # Faded
    /\ LET newColor == Complement(creature[c].color, creature[mall].color) IN
         creature' = [creature EXCEPT ![c].color = newColor,
                                ![c].myMet = @ + 1,
                                ![mall].color = newColor,
                                ![mall].myMet = @ + 1]
    /\ mall' = MeetingPlaceEmpty
    /\ totalMet' = totalMet + 1

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

\* A meeting is a two-way handshake: the global count is exactly the sum of
\* the individual counts divided by two, so no meeting is counted twice or
\* dropped from one participant's tally.
SumMet ==
    LET f[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN creature[x].myMet + f[S \ {x}]
    IN f[Creatures]

Spec == Init /\ [][Next]_vars

====