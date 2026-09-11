---- MODULE W4Od17m6p1t1 ----
EXTENDS Integers
CONSTANTS Bags, Nodes, MaxVer, MaxClock, LeaseDur
VARIABLES clock, holder, expiry, version, committed

TypeOK ==
  ( (clock \in 0 .. MaxClock)
   /\  (holder \in [Bags -> Nodes \cup {"none"}])
   /\  (expiry \in [Bags -> 0 .. MaxClock + LeaseDur])
   /\  (version \in [Bags -> 0 .. MaxVer])
   /\  (committed \subseteq [bag: Bags, seq: 1 .. MaxVer]))

Init ==
  ( (clock = 0)
   /\  (holder = [b \in Bags |-> "none"])
   /\  (expiry = [b \in Bags |-> 0])
   /\  (version = [b \in Bags |-> 0])
   /\  (committed = {}))

Acquire(n, b) ==
  ( ((holder[b] = "none" \/ clock >= expiry[b]))
   /\  (holder' = [holder EXCEPT ![b] = n])
   /\  (expiry' = [expiry EXCEPT ![b] = clock + LeaseDur])
   /\  (UNCHANGED <<clock, version, committed>>))

Update(n, b) ==
  ( (holder[b] = n)
   /\  (clock < expiry[b])
   /\  (version[b] < MaxVer)
   /\  (version' = [version EXCEPT ![b] = version[b] + 1])
   /\  (committed' = committed \cup {[bag |-> b, seq |-> version[b] + 1]})
   /\  (UNCHANGED <<clock, holder, expiry>>))

Release(b) ==
  ( (holder[b] # "none")
   /\  (holder' = [holder EXCEPT ![b] = "none"])
   /\  (UNCHANGED <<clock, expiry, version, committed>>))

Tick ==
  ( (clock < MaxClock)
   /\  (clock' = clock + 1)
   /\  (UNCHANGED <<holder, expiry, version, committed>>))

Next ==
  ( (\E n \in Nodes, b \in Bags : Acquire(n, b))
   \/  (\E n \in Nodes, b \in Bags : Update(n, b))
   \/  (\E b \in Bags : Release(b))
   \/  (Tick))

Spec == Init /\ [][Next]_<<clock, holder, expiry, version, committed>>

NoLostVersion ==
  \A b \in Bags :
    { c.seq : c \in { x \in committed : x.bag = b } } = (1 .. version[b])
====