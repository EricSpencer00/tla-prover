---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES state, mall, total

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
Color == {"blue", "red", "yellow"} \cup {Faded}
Creatures == 1..N
State == [c \in Creatures |-> [color : Color, met : Nat]]

\*--------------------------------------------------------------------
\* Complement rule
\*--------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE
      (c1 = "red" /\ c2 = "blue")  -> "yellow";
      (c1 = "blue" /\ c2 = "red")  -> "yellow";
      (c1 = "red" /\ c2 = "yellow") -> "blue";
      (c1 = "yellow" /\ c2 = "red") -> "blue";
      (c1 = "blue" /\ c2 = "yellow") -> "red";
      (c1 = "yellow" /\ c2 = "blue") -> "red";
    ENDCASE

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> [color |-> 
        CHOOSE col \in {"blue","red","yellow"} : TRUE,
        met |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
EnterEmpty ==
  /\ total < M
  /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ mall = MeetingPlaceEmpty
        /\ mall' = c
        /\ state' = state
        /\ total' = total

FadeOut ==
  /\ total >= M
  /\ mall = MeetingPlaceEmpty
  /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ \E c1 \in Creatures :
        /\ state[c1].color # Faded
        /\ c2 = mall
        /\ c1 # c2
        /\ LET newcol == Complement(state[c1].color, state[c2].color) IN
           /\ state' = [state EXCEPT
                ![c1] = [color |-> newcol, met |-> state[c1].met + 1],
                ![c2] = [color |-> newcol, met |-> state[c2].met + 1]]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total + 1

Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\*--------------------------------------------------------------------
\* Safety properties (invariants)
\*--------------------------------------------------------------------
TypeOK ==
  /\ state \in State
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total >= M) => (TotalMet == 2 * total)
TotalMet == 
  \A c \in Creatures : state[c].met

\*--------------------------------------------------------------------
\* Theorem (optional, for TLC)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeOK

====