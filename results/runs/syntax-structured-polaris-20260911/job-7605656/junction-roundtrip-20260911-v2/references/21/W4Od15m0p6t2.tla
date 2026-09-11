---- MODULE W4Od15m0p6t2 ----
EXTENDS Naturals
CONSTANTS Engines, MaxVer
VARIABLES ver, cached, ready, winner, winnerVer

vars == <<ver, cached, ready, winner, winnerVer>>

Init ==
  ( (ver = 0)
   /\  (cached = [e \in Engines |-> 0])
   /\  (ready = [e \in Engines |-> FALSE])
   /\  (winner = "none")
   /\  (winnerVer = 0))

Refresh(e) ==
  ( (cached' = [cached EXCEPT ![e] = ver])
   /\  (UNCHANGED <<ver, ready, winner, winnerVer>>))

Compute(e) ==
  ( (cached[e] = ver)
   /\  (ready' = [ready EXCEPT ![e] = TRUE])
   /\  (UNCHANGED <<ver, cached, winner, winnerVer>>))

Write(e) ==
  ( (ready[e] = TRUE)
   /\  (cached[e] = ver)
   /\  (ver < MaxVer)
   /\  (ver' = ver + 1)
   /\  (winner' = e)
   /\  (winnerVer' = ver)
   /\  (ready' = [ready EXCEPT ![e] = FALSE])
   /\  (UNCHANGED cached))

OrderFlow ==
  ( (ver < MaxVer)
   /\  (ver' = ver + 1)
   /\  (UNCHANGED <<cached, ready, winner, winnerVer>>))

Next == \E e \in Engines : Refresh(e) \/ Compute(e) \/ Write(e) \/ OrderFlow

Spec == Init /\ [][Next]_vars
NoStaleWriter == winner = "none" \/ cached[winner] >= winnerVer
====