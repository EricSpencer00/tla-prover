---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* concrete color symbols *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

Color == {Blue, Red, Yellow, Faded}
NonFadedColor == {Blue, Red, Yellow}

(* complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN Yellow
  ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN Red
  ELSE IF (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) THEN Blue
  ELSE Faded

VARIABLES state, meetingPlace, totalMeetings

(* each creature maps to a record with its colour and meeting count *)
StateRec == [color : Color, count : Nat]

Init ==
  /\ state \in [1..N -> StateRec]
  /\ \A i \in 1..N:
        /\ state[i].color \in NonFadedColor
        /\ state[i].count = 0
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E i \in 1..N:
        /\ state[i].color # Faded
        /\ meetingPlace' = i
        /\ UNCHANGED <<state, totalMeetings>>

Fade ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E i \in 1..N:
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i] = [color |-> Faded,
                                          count |-> @.count]]
        /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E i \in 1..N:
        /\ i # meetingPlace
        /\ state[i].color # Faded
        /\ state[meetingPlace].color # Faded
        /\ LET w == meetingPlace IN
           LET newC == Complement(state[i].color, state[w].color) IN
             /\ state' = [state EXCEPT
                          ![i] = [color |-> newC,
                                  count |-> @.count + 1],
                          ![w] = [color |-> newC,
                                  count |-> @.count + 1]]
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ Enter
  \/ Meet
  \/ Fade

vars == <<state, meetingPlace, totalMeetings>>

Spec == Init /\ [][Next]_vars

(* type correctness invariant *)
TypeOK ==
  /\ state \in [1..N -> StateRec]
  /\ meetingPlace \in {MeetingPlaceEmpty} \cup 1..N
  /\ totalMeetings \in Nat
  /\ \A i \in 1..N: state[i].color \in Color
  /\ (meetingPlace # MeetingPlaceEmpty => state[meetingPlace].color # Faded)

(* sum of individual meeting counts *)
SumCounts == Sum({i \in 1..N}, state[i].count)

(* safety property: when the global counter reaches the limit,
   the sum of all individual counts equals twice the limit *)
SumMet ==
  (totalMeetings = M) => (SumCounts = 2 * M)

====