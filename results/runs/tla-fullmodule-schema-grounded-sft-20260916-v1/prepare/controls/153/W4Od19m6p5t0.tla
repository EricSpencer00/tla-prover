---- MODULE W4Od19m6p5t0 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Copies, Patrons, LeaseTicks

\* A copy is offered under a lease with a countdown; a patron who goes quiet never
\* announces it, so only the countdown can free the copy again.
\* Collection is one-way: it discharges the patron's reservation coupon and removes
\* the copy from the shelf. The invariant is that a discharged coupon has left every
\* place from which a second collection could be started.

Unoffered == "unoffered"

VARIABLES shelf, lease, clock, waiting, discharged, quiet
vars == <<shelf, lease, clock, waiting, discharged, quiet>>

Stale == { c \in Copies : lease[c] # Unoffered /\ clock[c] = 0 }

TypeOK ==
  /\ shelf \subseteq Copies
  /\ lease \in [Copies -> Patrons \cup {Unoffered}]
  /\ clock \in [Copies -> 0..LeaseTicks]
  /\ waiting \subseteq Patrons
  /\ discharged \subseteq Patrons
  /\ quiet \subseteq Patrons

Init ==
  /\ shelf = Copies
  /\ lease = [c \in Copies |-> Unoffered]
  /\ clock = [c \in Copies |-> 0]
  /\ waiting = {}
  /\ discharged = {}
  /\ quiet = {}

Reserve(p) ==
  /\ p \notin waiting
  /\ p \notin discharged
  /\ \A c \in Copies : lease[c] # p
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<shelf, lease, clock, discharged, quiet>>

OfferCopy(c, p) ==
  /\ c \in shelf
  /\ lease[c] = Unoffered
  /\ p \in waiting
  /\ lease' = [lease EXCEPT ![c] = p]
  /\ clock' = [clock EXCEPT ![c] = LeaseTicks]
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED <<shelf, discharged, quiet>>

TickTimer ==
  /\ \E c \in Copies : lease[c] # Unoffered /\ clock[c] > 0
  /\ clock' = [c \in Copies |->
                 IF lease[c] # Unoffered /\ clock[c] > 0 THEN clock[c] - 1 ELSE clock[c]]
  /\ UNCHANGED <<shelf, lease, waiting, discharged, quiet>>

SweepLapsed ==
  /\ Stale # {}
  /\ lease' = [c \in Copies |-> IF c \in Stale THEN Unoffered ELSE lease[c]]
  /\ UNCHANGED <<shelf, clock, waiting, discharged, quiet>>

Collect(c) ==
  /\ lease[c] # Unoffered
  /\ clock[c] > 0
  /\ lease[c] \notin quiet
  /\ discharged' = discharged \cup {lease[c]}
  /\ lease' = [lease EXCEPT ![c] = Unoffered]
  /\ shelf' = shelf \ {c}
  /\ UNCHANGED <<clock, waiting, quiet>>

GoQuiet(p) ==
  /\ p \notin quiet
  /\ quiet' = quiet \cup {p}
  /\ UNCHANGED <<shelf, lease, clock, waiting, discharged>>

Resurface(p) ==
  /\ p \in quiet
  /\ quiet' = quiet \ {p}
  /\ UNCHANGED <<shelf, lease, clock, waiting, discharged>>

Next ==
  \/ \E p \in Patrons : Reserve(p) \/ GoQuiet(p) \/ Resurface(p)
  \/ \E c \in Copies, p \in Patrons : OfferCopy(c, p)
  \/ \E c \in Copies : Collect(c)
  \/ TickTimer
  \/ SweepLapsed

Spec == Init /\ [][Next]_vars /\ WF_vars(TickTimer) /\ WF_vars(SweepLapsed)

CouponsDischargeOnce ==
  \A p \in discharged : p \notin waiting /\ (\A c \in Copies : lease[c] # p)

LeasesAlwaysEnd ==
  \A c \in Copies : (lease[c] # Unoffered) ~> (lease[c] = Unoffered)
====