---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, mall, totalMeetings
vars == <<state, mall, totalMeetings>>

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE
       IN state[c][2] + SumOver(S \ {c})

TypeOK ==
  /\ state \in [Creatures -> Colors \X (0..M)]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ state \in [Creatures -> (Colors \ {Faded}) \X {0}]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(c) ==
  /\ state[c][1] # Faded
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ mall' = c
  /\ UNCHANGED <<state, totalMeetings>>

Fade(c) ==
  /\ state[c][1] # Faded
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state' = [state EXCEPT ![c] = <<Faded, state[c][2>>]
  /\ UNCHANGED <<mall, totalMeetings>>

Complement(a, b) ==
  IF a = b THEN a
  ELSE LET diff == {a, b}
       IN CHOOSE c \in Colors : c \notin diff

Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ totalMeetings < M
  /\ LET nw1 == Complement(state[c][1], state[mall][1])
         nw2 == Complement(state[mall][1], state[c][1])
     IN state' = [state EXCEPT ![c] = <<nw1, state[c][2] + 1>>, ![mall] = <<nw2, state[mall][2] + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  /\ (totalMeetings = M) => (SumOver(Creatures) = 2 * M)
  /\ (totalMeetings = M) <=> (mall = MeetingPlaceEmpty /\ \A c \in Creatures : state[c][1] = Faded)
====