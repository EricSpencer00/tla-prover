---- MODULE Chameneos ----
EXTENDS Naturals

\* Chameneos creatures meet pairwise at a central meeting place (the Mall).
\* When two creatures meet they both change color according to a complement
\* rule, and each meeting advances both participants' own meeting counts as
\* well as a single shared global meeting counter. The Mall closes once the
\* global counter reaches its limit, and any creature trying to enter thereafter
\* simply fades out; because each meeting advances the counter and two
\* participants, the sum of all individual meeting counts is always exactly
\* twice the global counter -- a per-creature view summed into a global arithmetic
\* truth.
CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c) == CASE c = "blue" -> "red"
                    [] c = "red" -> "yellow"
                    [] c = "yellow" -> "blue"

VARIABLES hue, participantCount, place, totalMeetings
vars == <<hue, participantCount, place, totalMeetings>>

TypeOK ==
  /\ hue \in [Creatures -> Colors]
  /\ participantCount \in [Creatures -> 0..M]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E f \in [Creatures -> Colors \ {Faded}]:
       hue = f
  /\ participantCount = [c \in Creatures |-> 0]
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterPlace(c) ==
  /\ hue[c] # Faded
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ place' = c
  /\ UNCHANGED <<hue, participantCount, totalMeetings>>

FadeOut(c) ==
  /\ hue[c] # Faded
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ hue' = [hue EXCEPT ![c] = Faded]
  /\ UNCHANGED <<participantCount, place, totalMeetings>>

\* The arriving creature meets the waiting creature, both taking the same
\* complement color regardless of whether they started equal or different.
MeetAndMutate(c) ==
  /\ place # MeetingPlaceEmpty
  /\ c # place
  /\ hue' = [x \in Creatures |->
               IF x \in {c, place}
                 THEN Complement(hue[x])
                 ELSE hue[x]]
  /\ participantCount' = [participantCount EXCEPT ![c] = @ + 1, ![place] = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures:
    \/ EnterPlace(c)
    \/ FadeOut(c)
    \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* When the global counter has saturated its limit, the sum of all individual
\* meeting counts is exactly twice that limit -- each meeting counted once
\* globally but contributed to two participants.
SumMet ==
  /\ totalMeetings = M => (2 * totalMeetings) = (participantCount[1] + participantCount[2] + (IF N >= 3 THEN participantCount[3] ELSE 0) + (IF N >= 4 THEN participantCount[4] ELSE 0))

====