---- MODULE Chameneos ----
\* A concurrency game modeling symmetrical cooperation among creatures (chameneos) that
\* meet pairwise at a central meeting place. Each meeting is a two-player encounter that
\* mutates both participants' colors together, so the running tally of pairwise meetings
\* is fully consistent: each meeting is counted exactly twice across the two participants.
\* A global meeting counter gates how many meetings may occur before the place closes.
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are indexed 1..N so they are comparable by identity; colors are a finite set.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES cstate, waiting, totalMeetings

vars == <<cstate, waiting, totalMeetings>>

\* cstate[c] = <<color, personal count>>: the mutable color and how many meetings c has joined.
TypeOK ==
  /\ cstate \in [Creatures -> [color : Colors, count : 0..M]]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ cstate \in [Creatures -> [color : {"blue", "red", "yellow"}, count : 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* The complement rule: given two colors, return the third distinct one (or leave a pair
\* of equals unchanged). The meeting place never holds two participants at once.
Complement(p, q) ==
  IF p = q THEN p
  ELSE LET r == {"blue", "red", "yellow"} \ {p, q} IN CHOOSE x \in r : TRUE

EnterEmpty(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ cstate[c].color # Faded
  /\ totalMeetings < M
  /\ waiting' = c
  /\ UNCHANGED <<cstate, totalMeetings>>

FadeOut(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ cstate[c].color # Faded
  /\ totalMeetings >= M
  /\ cstate' = [cstate EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<waiting, totalMeetings>>

Meet(d) ==
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # d
  /\ cstate[d].color # Faded
  /\ totalMeetings < M
  /\ LET newc == Complement(cstate[waiting].color, cstate[d].color) IN
       cstate' = [cstate EXCEPT ![waiting] = [color |-> newc, count |-> @.count + 1],
                  ![d] = [color |-> newc, count |-> @.count + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterEmpty(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E d \in Creatures : Meet(d)

Spec == Init /\ [][Next]_vars

\* SAFETY: each meeting is a two-way handshake, so the sum of every creature's personal
\* meeting count is exactly twice the global meeting counter -- no meeting lost, none invented.
SumMet ==
  LET sumPart(S) ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN cstate[x].count + sumPart(S \ {x})
  IN sumPart(Creatures) = 2 * totalMeetings

\* LIVENESS: once the meeting place has closed and is empty, every creature eventually
\* reaches its terminal faded state, so the system always drains to termination.
EventualFade ==
  (\A c \in Creatures : WF_vars(FadeOut(c))) /\ SF_vars(\E c \in Creatures : FadeOut(c))

====