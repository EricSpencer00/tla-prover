------------------------- MODULE Chameneos -------------------------
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}
Entries == [color : Colors, meets : 0 .. M]

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

Complement(a, b) ==
  IF a = b THEN a
  ELSE LET c == {"blue", "red", "yellow"} IN CHOOSE k \in c : k # a /\ k # b

VARIABLES state, waiting, total
vars == <<state, waiting, total>>

TypeOK ==
  /\ state \in [Creatures -> Entries]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0 .. M

Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE cl \in {"blue", "red", "yellow"} : TRUE, meets |-> 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ total = 0

EnterPlace(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ total < M
  /\ state[c].color # Faded
  /\ waiting' = c
  /\ UNCHANGED <<state, total>>

FadeOut(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ total >= M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<waiting, total>>

MeetAndMutate(c) ==
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # c
  /\ waiting # MeetingPlaceEmpty
  /\ state[c].color # Faded
  /\ state[waiting].color # Faded
  /\ total < M
  /\ LET newcol == Complement(state[c].color, state[waiting].color) IN
       state' = [state EXCEPT ![c] = [color |-> newcol, meets |-> @.meets + 1],
                            ![waiting] = [color |-> newcol, meets |-> @.meets + 1]]
  /\ total' = total + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  total >= M => SumOver([c \in Creatures |-> state[c].meets], Creatures) = 2 * total
=============================================================================