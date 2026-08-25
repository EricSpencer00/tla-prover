---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ------------------------------------------------------------------ *)
(* Colors *)
Blue \in Color == TRUE
Red  \in Color == TRUE
Yellow \in Color == TRUE
Faded \in Color == TRUE

Color == {Blue, Red, Yellow, Faded}

(* ------------------------------------------------------------------ *)
(* State variables *)
VARIABLES status, mall, totalMeetings

(* ------------------------------------------------------------------ *)
(* Helper: complement rule *)
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

(* ------------------------------------------------------------------ *)
(* Initial state *)
Init ==
  /\ status = [c \in 1..N |-> 
        [color |-> CHOOSE col \in {Blue, Red, Yellow} : TRUE,
         meetCount |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

(* ------------------------------------------------------------------ *)
(* Actions *)

EnterEmpty(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ c \in 1..N
  /\ status[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<status, totalMeetings>>

FadeOut(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ c \in 1..N
  /\ status[c].color # Faded
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, totalMeetings>>

Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ c \in 1..N
  /\ c # mall
  /\ status[c].color # Faded
  /\ status[mall].color # Faded
  /\ LET newCol == Complement(status[c].color, status[mall].color) IN
        /\ status' = [status EXCEPT
               ![c].color = newCol,
               ![c].meetCount = @ + 1,
               ![mall].color = newCol,
               ![mall].meetCount = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in 1..N : EnterEmpty(c)
  \/ \E c \in 1..N : FadeOut(c)
  \/ \E c \in 1..N : Meet(c)

(* ------------------------------------------------------------------ *)
(* Specification *)
Spec == Init /\ [][Next]_<<status, mall, totalMeetings>>

(* ------------------------------------------------------------------ *)
(* Invariants *)

TypeOK ==
  /\ status \in [1..N -> [color : Color, meetCount : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat

SumMet ==
  (totalMeetings = M) => 
    (Sum([c \in 1..N] status[c].meetCount) = 2 * M)

====