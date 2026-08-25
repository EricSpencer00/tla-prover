---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--- Colors ---------------------------------------------------*)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"
Colors == {Blue, Red, Yellow}
AllColors == Colors \cup {Faded}

(*--- State variables ------------------------------------------*)
VARIABLES state, mall, total

(*--- Record type for each creature -----------------------------*)
StateRecord == [color : AllColors, met : Nat]

(*--- Initial state --------------------------------------------*)
Init ==
  /\ state \in [1..N -> StateRecord]
  /\ \A i \in 1..N:
        /\ state[i].color \in Colors
        /\ state[i].met = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(*--- Complement rule ------------------------------------------*)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN Yellow
  ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
  ELSE Blue      \* remaining case: Red and Yellow

(*--- Actions --------------------------------------------------*)
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N:
        /\ state[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<state, total>>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E i \in 1..N:
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N:
        /\ i # mall
        /\ state[i].color # Faded
        /\ state[mall].color # Faded
        LET newc == Complement(state[i].color, state[mall].color) IN
          /\ state' = [state EXCEPT
                ![i]   = [color |-> newc, met |-> @.met + 1],
                ![mall] = [color |-> newc, met |-> @.met + 1]]
          /\ total' = total + 1
          /\ mall' = MeetingPlaceEmpty

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet

(*--- Specification --------------------------------------------*)
Spec == Init /\ [][Next]_<<state, mall, total>>

(*--- Invariants ----------------------------------------------*)
TypeOK ==
  /\ state \in [1..N -> StateRecord]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total = M) => (\SUM i \in 1..N: state[i].met) = 2 * M

====