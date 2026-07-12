---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty
(* N   : number of creatures (identifiers 1..N)
   M   : maximum number of meetings before the meeting place closes
   Faded : the faded color value
   MeetingPlaceEmpty : the empty marker for the meeting place *)

(* Derived constants *)
Creatures == 1..N
Colors == {Red, Blue, Yellow, Faded}
Waiting == [c \in Creatures |-> MeetingPlaceEmpty]

VARIABLES state, meetingPlace, totalMeetings

(* state maps each creature to a pair [color, meetingCount] *)
(* meetingPlace is either MeetingPlaceEmpty or a creature identifier *)

(* Initial condition *)
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE color \in {Red, Blue, Yellow} : color, count |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

(* Complement rule applied to two different colors *)
Complement[c1, c2] ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE c \in {Red, Blue, Yellow} : c # c1 /\ c # c2

(* Action: a non-faded creature enters an empty meeting place *)
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ meetingPlace' = c
          /\ UNCHANGED <<state, totalMeetings>>
    /\ UNCHANGED <<state, totalMeetings>>

(* Action: a non-faded creature tries to enter after meet limit reached *)
FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<meetingPlace, totalMeetings>>
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

(* Action: an arriving creature meets the waiting creature *)
MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c1, c2 \in Creatures :
          /\ c1 # c2
          /\ meetingPlace = c1
          /\ state[c1].color # Faded
          /\ state[c2].color # Faded
          /\ newColor = Complement[state[c1].color, state[c2].color]
          /\ state' = [state EXCEPT ![c1].color = newColor,
                                      ![c1].count = state[c1].count + 1,
                                      ![c2].color = newColor,
                                      ![c2].count = state[c2].count + 1]
          /\ meetingPlace' = MeetingPlaceEmpty
          /\ totalMeetings' = totalMeetings + 1
          /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

Spec == Init /\ [][Next]_<<state, meetingPlace, totalMeetings>>

(* Type invariant: all variables have the expected types *)
TypeOK ==
    /\ state \in [Creatures |-> [color : Colors, count : Nat]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

(* Safety invariant: when the global counter reaches M, the sum of individual counts equals 2*M *)
SumMet ==
    totalMeetings = M => Sum([state[c].count |-> c \in Creatures]) = 2 * M

====