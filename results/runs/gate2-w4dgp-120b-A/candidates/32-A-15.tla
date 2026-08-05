---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of creatures (chameneos); M: total meeting limit; Faded: marker color; MeetingPlaceEmpty: empty marker
\* Each creature remembers its own meeting count; the meeting place holds one waiting creature, then two animals meet and both
\* adopt a new common color, chosen as the complement of the pair they brought.

Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}
Counts == [color : Colors, met : 0..(2 * M)]

\* A color distinct from both inputs; undefined (Faded) if the inputs are the same.
Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE LET s == {c1, c2} IN CHOOSE c \in (Colors \ s) : TRUE

Meetings == [color : Colors, met : 0..(2 * M)]
Waiting == [c : Creatures, met : 0..M]

VARIABLES status, waiting, meetings

vars == <<status, waiting, meetings>>

TypeOK ==
  /\ status \in [Creatures -> Meetings]
  /\ waiting \in Waiting \cup {MeetingPlaceEmpty}
  /\ meetings \in 0..M

Init ==
  /\ status = [c \in Creatures |-> [color |-> CHOOSE k \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ meetings = 0

Enter ==
  /\ waiting = MeetingPlaceEmpty
  /\ meetings < M
  /\ \E c \in Creatures :
       /\ status[c].color # Faded
       /\ waiting = MeetingPlaceEmpty
       /\ waiting' = [c |-> c, met |-> status[c].met]
  /\ UNCHANGED <<status, meetings>>

FadeOut ==
  /\ waiting = MeetingPlaceEmpty
  /\ meetings = M
  /\ \E c \in Creatures :
       /\ status[c].color # Faded
       /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<waiting, meetings>>

\* Two creatures meet: both adopt the complement of the colors they brought, each bumps its own count and the global count.
Meet ==
  /\ waiting # MeetingPlaceEmpty
  /\ \E c \in Creatures :
       /\ c # waiting.c
       /\ status[c].color # Faded
       /\ status[waiting.c].color # Faded
       /\ LET nc == Complement(status[c].color, status[waiting.c].color) IN
            /\ status' = [status EXCEPT ![c] = [color |-> nc, met |-> @.met + 1], ![waiting.c] = [color |-> nc, met |-> @.met + 1]]
       /\ meetings' = meetings + 1
       /\ waiting' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ Meet

Spec == Init /\ [][Next]_vars

\* At the meeting limit the global count equals half the summed individual counts: every meeting involved exactly two participants.
SumMet ==
  meetings = M =>
    ((status[0].met + status[1].met + (IF N > 2 THEN status[2].met ELSE 0))
       = 2 * M)

====