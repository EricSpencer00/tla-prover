---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants required by the configuration
---------------------------------------------------------------------*)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Color definitions (including the faded color)
---------------------------------------------------------------------*)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"
Colors == {Blue, Red, Yellow, Faded}

(*--------------------------------------------------------------------
  State variables
---------------------------------------------------------------------*)
VARIABLES state, mall, total

(*--------------------------------------------------------------------
  Helper: complement rule for two colors
---------------------------------------------------------------------*)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE 
    CASE /\ (c1 = Blue  /\ c2 = Red)    \/ (c1 = Red    /\ c2 = Blue)    THEN Yellow
       [] /\ (c1 = Blue  /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue)   THEN Red
       [] /\ (c1 = Red   /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red)    THEN Blue
       [] OTHER -> Faded  \* should never happen

(*--------------------------------------------------------------------
  Initialization
---------------------------------------------------------------------*)
Init ==
  /\ state \in [1..N -> [color : {Blue, Red, Yellow}, meetCount : Nat]]
  /\ \A i \in 1..N: state[i].meetCount = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(*--------------------------------------------------------------------
  Action: a non‑faded creature enters an empty meeting place
---------------------------------------------------------------------*)
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<state, total>>

(*--------------------------------------------------------------------
  Action: a creature fades out when the meeting limit has been reached
---------------------------------------------------------------------*)
FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

(*--------------------------------------------------------------------
  Action: two different non‑faded creatures meet and mutate
---------------------------------------------------------------------*)
MeetAndMutate ==
  /\ mall \in 1..N
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # mall
        /\ state[i].color # Faded
        /\ state[mall].color # Faded
        LET c1   == state[i].color
            c2   == state[mall].color
            newc == Complement(c1, c2)
        IN
          /\ state' = [state EXCEPT 
                ![i].color      = newc,
                ![i].meetCount  = @ + 1,
                ![mall].color   = newc,
                ![mall].meetCount = @ + 1]
          /\ total' = total + 1
          /\ mall'  = MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Next-state relation
---------------------------------------------------------------------*)
Next ==
  \/ Enter
  \/ FadeOut
  \/ MeetAndMutate

(*--------------------------------------------------------------------
  Specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<state, mall, total>>

(*--------------------------------------------------------------------
  Type correctness invariant
---------------------------------------------------------------------*)
TypeOK ==
  /\ state \in [1..N -> [color : Colors, meetCount : Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat

(*--------------------------------------------------------------------
  Safety invariant: when total meetings reach the limit, the sum of
  individual meeting counts equals twice the limit.
---------------------------------------------------------------------*)
SumMet ==
  (total = M) => 
    LET cnts == { state[i].meetCount : i \in 1..N } IN
      Sum(cnts) = 2 * M

====