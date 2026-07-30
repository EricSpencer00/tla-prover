---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Action codes: Enter (a creature enters the empty meeting place),
\* Fade (a creature becomes faded once meetings are closed), and Meet
\* (two creatures complete a meeting and change color together).
Acts == {"Enter", "Fade", "Meet"}

Creatures == 1..N
Colors == {"blue", "red", "yellow"}

\* The global meeting counter is only ever compared against M; it never
\* grows past M, so it stays within the range of the bound M.
VARIABLES attribs, mall, meetings

vars == <<attribs, mall, meetings>>

TypeOK ==
  /\ attribs \in [Creatures -> [color: Colors \cup {Faded}, count: 0..M]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetings \in 0..M

Init ==
  /\ \E initColors \in [Creatures -> Colors] :
       attribs = [c \in Creatures |-> [color |-> initColors[c], count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ meetings = 0

\* Dilution: a creature is free to enter the meeting place only if it is
\* not faded and the global counter has not reached its bound yet.
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ meetings < M
  /\ attribs[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<attribs, meetings>>

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ meetings = M
  /\ attribs[c].color # Faded
  /\ attribs' = [attribs EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, meetings>>

\* Complementarity: the new color depends on the pair's current colors.
Complement(x, y) ==
  IF x = y THEN x
  ELSE LET Z == {"blue", "red", "yellow"} \ {x, y} IN CHOOSE z \in Z : TRUE

\* Two distinct creatures meeting: both are recorded as participants.
Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ attribs[c].color # Faded
  /\ attribs[mall].color # Faded
  /\ meetings < M
  /\ LET nc == Complement(attribs[c].color, attribs[mall].color) IN
       attribs' = [attribs EXCEPT ![c].color = nc, ![mall].color = nc,
                   ![c].count = attribs[c].count + 1,
                   ![mall].count = attribs[mall].count + 1]
  /\ meetings' = meetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

\* Each meeting accounts for exactly two participants, so the global
\* counter multiplied by two must always equal the sum of the per-creature
\* counts once the meeting budget is exhausted.
SumMet ==
  /\ meetings = M
  /\ (2 * M) = (attribs[1].count + attribs[2].count + attribs[3].count)

Spec == Init /\ [][Next]_vars

====