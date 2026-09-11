---- MODULE W4Od13m1p5t5 ----
EXTENDS Naturals, FiniteSets

\* Vending machines sit on a circulating-token ring.  A single promotional
\* item exists network-wide; dispensing it is irreversible, so the ledger
\* records exactly which machine consumed it.
CONSTANTS N, MaxOverrides

Machines == 1..N
None == 0
Nxt(m) == (m % N) + 1

VARIABLES holder, waiting, asked, dispensed, redeemer, overrides
vars == <<holder, waiting, asked, dispensed, redeemer, overrides>>

TypeOK ==
  ( (holder \in Machines)
   /\  (waiting \subseteq Machines)
   /\  (asked \subseteq Machines)
   /\  (dispensed \subseteq Machines)
   /\  (redeemer \in Machines \cup {None})
   /\  (overrides \in 0..MaxOverrides))

Init ==
  ( (holder = 1)
   /\  (waiting = {})
   /\  (asked = {})
   /\  (dispensed = {})
   /\  (redeemer = None)
   /\  (overrides = MaxOverrides))

\* A customer walks up to a machine that has not yet taken a promo request.
Request ==
  ( (\E m \in Machines :
       ( (m \notin asked)
        /\  (asked' = asked \cup {m})
        /\  (waiting' = waiting \cup {m})))
   /\  (UNCHANGED <<holder, dispensed, redeemer, overrides>>))

Circulate ==
  ( (holder' = Nxt(holder))
   /\  (UNCHANGED <<waiting, asked, dispensed, redeemer, overrides>>))

\* The promo is still unclaimed, so the token holder physically dispenses it
\* and writes itself into the network ledger.
Redeem ==
  ( (holder \in waiting)
   /\  (redeemer = None)
   /\  (dispensed' = dispensed \cup {holder})
   /\  (redeemer' = holder)
   /\  (waiting' = waiting \ {holder})
   /\  (UNCHANGED <<holder, asked, overrides>>))

Decline ==
  ( (holder \in waiting)
   /\  (redeemer # None)
   /\  (waiting' = waiting \ {holder})
   /\  (UNCHANGED <<holder, asked, dispensed, redeemer, overrides>>))

Serve == Redeem \/ Decline

\* A field technician's master key may relocate the token, bypassing ring
\* order, but the key has a limited number of uses.
AdminRelocate ==
  ( (overrides > 0)
   /\  (\E m \in Machines :
       ( (m # holder)
        /\  (holder' = m)))
   /\  (overrides' = overrides - 1)
   /\  (UNCHANGED <<waiting, asked, dispensed, redeemer>>))

Next == Request \/ Circulate \/ Redeem \/ Decline \/ AdminRelocate

Spec == Init /\ [][Next]_vars /\ WF_vars(Circulate) /\ SF_vars(Serve)

\* Every machine that actually put the promo item in a customer's hands is
\* the single machine the ledger names, so the item leaves stock once.
OneTimeDispense == \A m \in dispensed : m = redeemer

EveryRequestResolved == \A m \in Machines : (m \in waiting) ~> (m \notin waiting)
====