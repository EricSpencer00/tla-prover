---- MODULE W4Od1m7p3t2 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Slots, Flights, Instances, Free

VARIABLES reg, scratch, target, held
vars == << reg, scratch, target, held >>

TypeOK ==
  ( (reg \in [Slots -> Flights \cup {Free}])
   /\  (scratch \in [Instances -> [Slots -> Flights \cup {Free}]])
   /\  (target \in [Instances -> Flights \cup {Free}])
   /\  (held \in [Flights -> Slots \cup {Free}]))

Init ==
  ( (reg = [s \in Slots |-> Free])
   /\  (scratch = [i \in Instances |-> [s \in Slots |-> Free]])
   /\  (target = [i \in Instances |-> Free])
   /\  (held = [f \in Flights |-> Free]))

PickFlight(i, f) ==
  ( (target[i] = Free)
   /\  (held[f] = Free)
   /\  (\A j \in Instances : target[j] # f)
   /\  (target' = [target EXCEPT ![i] = f])
   /\  (UNCHANGED << reg, scratch, held >>))

ReadSlot(i, s) ==
  ( (target[i] # Free)
   /\  (scratch' = [scratch EXCEPT ![i][s] = reg[s]])
   /\  (UNCHANGED << reg, target, held >>))

SwapClaim(i, s) ==
  ( (target[i] # Free)
   /\  (scratch[i][s] = Free)
   /\  (reg[s] = Free)
   /\  (reg' = [reg EXCEPT ![s] = target[i]])
   /\  (held' = [held EXCEPT ![target[i]] = s])
   /\  (target' = [target EXCEPT ![i] = Free])
   /\  (scratch' = [scratch EXCEPT ![i][s] = target[i]]))

SwapFails(i, s) ==
  ( (target[i] # Free)
   /\  (scratch[i][s] # reg[s])
   /\  (scratch' = [scratch EXCEPT ![i][s] = reg[s]])
   /\  (UNCHANGED << reg, target, held >>))

ReleaseSlot(i, f) ==
  ( (held[f] \in Slots)
   /\  (reg[held[f]] = f)
   /\  (scratch[i][held[f]] = f)
   /\  (reg' = [reg EXCEPT ![held[f]] = Free])
   /\  (held' = [held EXCEPT ![f] = Free])
   /\  (scratch' = [scratch EXCEPT ![i][held[f]] = Free])
   /\  (UNCHANGED << target >>))

Next ==
  ( (\E i \in Instances, f \in Flights : PickFlight(i, f) \/ ReleaseSlot(i, f))
   \/  (\E i \in Instances, s \in Slots : ReadSlot(i, s) \/ SwapClaim(i, s) \/ SwapFails(i, s)))

Spec == Init /\ [][Next]_vars

AllocationOK ==
  ( (\A s1, s2 \in Slots :
       (reg[s1] # Free /\ reg[s1] = reg[s2]) => s1 = s2)
   /\  (\A f \in Flights : (held[f] \in Slots) => reg[held[f]] = f)
   /\  (\A s \in Slots : (reg[s] \in Flights) => held[reg[s]] = s)
   /\  (\A i \in Instances : target[i] \in Flights => held[target[i]] = Free))
====