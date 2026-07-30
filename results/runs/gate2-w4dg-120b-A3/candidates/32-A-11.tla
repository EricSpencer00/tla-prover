---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature carries its color together with the number of meetings it
\* has participated in; this joint value is what the invariant inspects.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Metamet == [col : Colors, done : 0..M]

RECURSIVE SumMetOver(_)
SumMetOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN Metamet[x].done + SumMetOver(S \ {x})

VARIABLES state, place, total

vars == <<state, place, total>>

TypeOK ==
  /\ state \in [Creatures -> Metamet]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ \E c \in [Creatures -> Colors] :
        state = [k \in Creatures |-> [col |-> c[k], done |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* Colors both keep when equal; otherwise both adopt the third colour.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET S == {a, b} IN CHOOSE c \in Colors :
         /\ c \notin S
         /\ c # Faded

\* A creature that cannot enter because meetings have run out fades out,
\* keeping whatever meeting count it already had.
Fade(k) == [col |-> Faded, done |-> state[k].done]

Enter(k) ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ state[k].col # Faded
  /\ place' = k
  /\ UNCHANGED <<state, total>>

FadeOut(k) ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ state[k].col # Faded
  /\ state' = [state EXCEPT ![k] = Fade(k)]
  /\ UNCHANGED <<place, total>>

MeetAndMutate(k) ==
  /\ place # MeetingPlaceEmpty
  /\ place # k
  /\ state[place].col # Faded
  /\ LET c == Complement(state[place].col, state[k].col) IN
       /\ state' = [state EXCEPT ![place] = [col |-> c, done |-> @.done + 1],
                              ![k] = [col |-> c, done |-> @.done + 1]]
  /\ place' = MeetingPlaceEmpty
  /\ total' = total + 1

Next ==
  \/ \E k \in Creatures : Enter(k)
  \/ \E k \in Creatures : FadeOut(k)
  \/ \E k \in Creatures : MeetAndMutate(k)

Spec == Init /\ [][Next]_vars

\* Conservation: when the meeting place is closed, every meeting is
\* accounted for exactly twice -- once for each participant.
SumMet == (total = M) => (SumMetOver(Creatures) = 2 * M)
====