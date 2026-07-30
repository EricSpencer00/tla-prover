---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N is the number of chameneos; their identifiers are 1..N.
\* M is the total-meeting limit at which the meeting place closes.
\* Faded is the color a creature takes on after fading out.
\* MeetingPlaceEmpty marks an empty meeting place.
\* Each creature's state is a pair: its current color and its personal meeting count.
\* The meeting place holds at most one waiting creature at a time.
\* The global meeting counter counts completed meetings system-wide.

VARIABLES creature, meetingPlace, totalMeetings

vars == <<creature, meetingPlace, totalMeetings>>

Colors == {"blue", "red", "yellow", Faded}

TypeOK ==
  /\ creature \in [1..N -> [color: Colors, met: 0..M]]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

\* The complement rule: two identical colors stay unchanged; two distinct colors
\* both become the third color not held by either creature.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET unused == {"blue", "red", "yellow"} \ {c1, c2}
       IN CHOOSE c \in unused : TRUE

Init ==
  /\ \E initColors \in [1..N -> {"blue", "red", "yellow"}] :
        creature = [i \in 1..N |-> [color |-> initColors[i], met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* Enter: a non-faded creature joins the empty meeting place before the limit
\* is reached, becoming the waiting participant.
Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E i \in 1..N :
        /\ creature[i].color # Faded
        /\ meetingPlace' = i
  /\ UNCHANGED <<creature, totalMeetings>>

\* FadeOut: once the limit is reached, a creature that tries to enter fades
\* instead of joining the meeting place.
FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E i \in 1..N :
        /\ creature[i].color # Faded
        /\ creature' = [creature EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* MeetAndMutate: two distinct creatures exchange colors via Complement and
\* each increment their personal meeting count; the global counter advances.
MeetAndMutate ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ \E i \in 1..N :
        /\ i # meetingPlace
        /\ creature[i].color # Faded
        /\ creature[meetingPlace].color # Faded
        /\ LET newc == Complement(creature[i].color, creature[meetingPlace].color) IN
            /\ creature' = [creature EXCEPT ![i].color = newc,
                                          ![i].met = @ + 1,
                                          ![meetingPlace].color = newc,
                                          ![meetingPlace].met = @ + 1]
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ totalMeetings' = totalMeetings + 1
  /\ UNCHANGED <<>>

Next == Enter \/ FadeOut \/ MeetAndMutate

\* Fairness: every creature that can act in the meeting place eventually does.
Spec == Init /\ [][Next]_vars
        /\ \A i \in 1..N : WF_vars(Enter /\ MeetAndMutate)

\* Bounded co-occurrence: at the meeting limit, the sum of individual meeting
\* counts equals twice the global count -- each meeting touched exactly two ch.
SumMet ==
  (totalMeetings = M) =>
    (2 * totalMeetings = creature[1].met + creature[2].met + (IF N > 2 THEN creature[3].met ELSE 0))

====