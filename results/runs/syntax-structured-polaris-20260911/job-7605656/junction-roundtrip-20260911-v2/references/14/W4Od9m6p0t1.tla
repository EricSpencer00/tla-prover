---- MODULE W4Od9m6p0t1 ----
EXTENDS Naturals
CONSTANTS Controllers, MaxClock, NONE
VARIABLES clock, leaseHolder, leaseExp, inbox, shedding
vars == <<clock, leaseHolder, leaseExp, inbox, shedding>>

Init ==
  ( (clock = 0)
   /\  (leaseHolder = NONE)
   /\  (leaseExp = 0)
   /\  (inbox = {})
   /\  (shedding = [c \in Controllers |-> FALSE]))

Request(c) ==
  ( (c \notin inbox)
   /\  (~shedding[c])
   /\  (inbox' = inbox \cup {c})
   /\  (UNCHANGED <<clock, leaseHolder, leaseExp, shedding>>))

Grant(c) ==
  ( (c \in inbox)
   /\  (leaseHolder = NONE)
   /\  (leaseHolder' = c)
   /\  (leaseExp' = clock + 2)
   /\  (shedding' = [shedding EXCEPT ![c] = TRUE])
   /\  (inbox' = inbox \ {c})
   /\  (UNCHANGED clock))

ReleaseMsg(c) ==
  ( (leaseHolder = c)
   /\  (shedding[c])
   /\  (leaseHolder' = NONE)
   /\  (leaseExp' = 0)
   /\  (shedding' = [shedding EXCEPT ![c] = FALSE])
   /\  (UNCHANGED <<clock, inbox>>))

Tick ==
  ( (clock < MaxClock)
   /\  (clock' = clock + 1)
   /\  (IF leaseHolder # NONE /\ clock + 1 >= leaseExp
       THEN ( (leaseHolder' = NONE)
             /\  (leaseExp' = 0)
             /\  (shedding' = [c \in Controllers |-> FALSE]))
       ELSE UNCHANGED <<leaseHolder, leaseExp, shedding>>)
   /\  (UNCHANGED inbox))

Next ==
  ( (\E c \in Controllers: Request(c))
   \/  (\E c \in Controllers: Grant(c))
   \/  (\E c \in Controllers: ReleaseMsg(c))
   \/  (Tick))

Spec == Init /\ [][Next]_vars

SoleValidShedder ==
  \A c \in Controllers: shedding[c] => (leaseHolder = c /\ clock < leaseExp)
====