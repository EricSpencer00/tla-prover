---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANTS Blue, Red, Yellow

VARIABLES state, mall, gCount

(* ---------------------------------------------------------------------- *)
(* Sets of colors *)

Colors   == {Blue, Red, Yellow}
AllColors == Colors \cup {Faded}

(* ---------------------------------------------------------------------- *)
(* Complement rule *)

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN Yellow
  ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
  ELSE IF (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) THEN Blue
  ELSE Faded   \* should never be reached for valid inputs

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ state = [i \in 1..N |-> [color |-> CHOOSE c \in Colors : TRUE,
                              cnt   |-> 0]]
  /\ mall   = MeetingPlaceEmpty
  /\ gCount = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ gCount < M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = state
        /\ mall'   = i
        /\ gCount' = gCount

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ gCount >= M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ mall'   = MeetingPlaceEmpty
        /\ gCount' = gCount

Meet ==
  LET j == mall IN
    /\ j # MeetingPlaceEmpty
    /\ j \in 1..N
    /\ gCount < M
    /\ \E i \in 1..N :
          /\ i # j
          /\ state[i].color # Faded
          /\ state[j].color # Faded
          /\ LET newCol == Complement(state[i].color, state[j].color) IN
               /\ state' = [state EXCEPT
                              ![i] = [color |-> newCol,
                                      cnt   |-> state[i].cnt + 1],
                              ![j] = [color |-> newCol,
                                      cnt   |-> state[j].cnt + 1]]
               /\ mall'   = MeetingPlaceEmpty
               /\ gCount' = gCount + 1

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec ==
  Init /\ [][Next]_<<state, mall, gCount>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
  /\ state \in [1..N -> [color : AllColors, cnt : Nat]]
  /\ mall   \in (1..N) \cup {MeetingPlaceEmpty}
  /\ gCount \in Nat
  /\ gCount <= M

SumMet ==
  (gCount = M) => ((+/ i \in (1..N) : state[i].cnt) = 2 * M)

====