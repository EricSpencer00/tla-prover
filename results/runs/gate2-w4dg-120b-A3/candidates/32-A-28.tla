---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES colors, place, total

vars == <<colors, place, total>>

Participants == 0 .. M
Colors == {"blue", "red", "yellow", Faded}

NONE == "none"

TypeOK ==
  /\ colors \in [1 .. N -> Colors \X Participants]
  /\ place \in (1 .. N) \cup {MeetingPlaceEmpty}
  /\ total \in Participants

Init ==
  /\ colors = [c \in 1 .. N |-> CHOOSE col \in Colors \ {{Faded}} :
                          \E v \in 0 .. M : <<col, v>> \in colors]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* Complement rule: same color stays, different colors become the third one.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE { "blue", "red", "yellow" } \ {c1, c2}

\* A creature that cannot enter (meeting place closed, no partner) fades.
\* It keeps its meeting count so the sum check below stays exact.
FadeOut(c) ==
  /\ colors[c][1] # Faded
  /\ colors' = [colors EXCEPT ![c] = <<Faded, colors[c][2]>>]
  /\ UNCHANGED <<place, total>>

Enter(c) ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ colors[c][1] # Faded
  /\ place' = c
  /\ UNCHANGED <<colors, total>>

Meet(a, b) ==
  /\ place = b
  /\ a # b
  /\ colors[a][1] # Faded
  /\ total < M
  /\ colors' = [colors EXCEPT ![a] = <<Complement(colors[a][1], colors[b][1]), colors[a][2] + 1>>,
                           ![b] = <<Complement(colors[a][1], colors[b][1]), colors[b][2] + 1>>]
  /\ total' = total + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in 1 .. N : Enter(c)
  \/ \E a \in 1 .. N, b \in 1 .. N : Meet(a, b)
  \/ \E c \in 1 .. N : FadeOut(c)

Spec == Init /\ [][Next]_vars

\* Participants is a conserved quantity: each meeting consumes two slots of
\* individual participation, so at the limit the sum equals exactly 2M.
SumMet ==
  LET f[S \in SUBSET (1 .. N)] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN colors[x][2] + f[S \ {x}]
  IN f[1 .. N] = 2 * total

====