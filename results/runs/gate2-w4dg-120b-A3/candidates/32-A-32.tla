---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature's state is a pair: its current color and its individual meeting count.
\* The meeting place may hold at most one waiting creature at a time.
\* The global meeting counter tracks how many meetings the system has completed.

VARIABLES pair, place, global

vars == <<pair, place, global>>

\* Colors in the game; the complement rule below assumes exactly these three body colors.
Colors == {"blue", "red", "yellow"}
\* Mapping from a pair of distinct body colors to their complement (third color). It is
\* deliberately partial: a creature meeting itself is not covered here and is not allowed.
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

TypeOK ==
  /\ pair \in [1..N -> (Colors \cup {Faded}) \X (0..M)]
  /\ place \in (1..N) \cup {MeetingPlaceEmpty}
  /\ global \in 0..M

Init ==
  /\ pair \in [1..N -> (Colors \cup {Faded}) \X (0..M)]
  /\ place = MeetingPlaceEmpty
  /\ global = 0

\* A non-faded creature enters an empty meeting place before the meeting limit is reached.
Enter ==
  /\ place = MeetingPlaceEmpty
  /\ global < M
  /\ \E c \in 1..N :
       /\ pair[c][1] # Faded
       /\ place' = c
  /\ UNCHANGED <<pair, global>>

\* Once the meeting limit has been reached, a creature that tries to enter fades out.
FadeOut ==
  /\ place = MeetingPlaceEmpty
  /\ global = M
  /\ \E c \in 1..N :
       /\ pair[c][1] # Faded
       /\ pair' = [pair EXCEPT ![c] = <<Faded, pair[c][2]>>]
  /\ UNCHANGED <<place, global>>

\* Two distinct creatures meet: both adopt their complement color, both gain a meeting,
\* the global counter advances, and the meeting place empties.
MeetAndMutate ==
  /\ place # MeetingPlaceEmpty
  /\ \E c \in 1..N :
       /\ c # place
       /\ pair[c][1] # Faded
       /\ pair[place][1] # Faded
       /\ LET newc == Complement(pair[c][1], pair[place][1]) IN
            /\ pair' = [pair EXCEPT ![c] = <<newc, pair[c][2] + 1>>, ![place] = <<newc, pair[place][2] + 1>>]
  /\ global' = global + 1
  /\ place' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

\* Conservation: when no further meetings can start, every creature's meeting count
\* accounts for exactly its part of a completed meeting, so the sum is twice the total.
SumMet ==
  (global = M) => (LET f[S \in SUBSET (1..N)] ==
                       IF S = {} THEN 0
                       ELSE LET x == CHOOSE y \in S : TRUE
                            IN pair[x][2] + f[S \ {x}]
                    IN f[1..N]) = 2 * global

====