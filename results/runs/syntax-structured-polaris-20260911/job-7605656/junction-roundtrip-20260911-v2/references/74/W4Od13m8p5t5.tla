---- MODULE W4Od13m8p5t5 ----
EXTENDS Naturals

CONSTANTS Orders, Slots, NoOrder, NoSlot

VARIABLES bus, arm, served, credit, tech

vars == <<bus, arm, served, credit, tech>>

\* Two levels of lock: the machine bus must be taken before any slot motor
\* can be armed, and the bus is handed straight back once a motor is armed.
\* Turning a motor drops product, which cannot be taken back.

Armed(o) == \E s \in Slots : arm[s] = o

TypeOK ==
  ( (bus \in Orders \cup {NoOrder})
   /\  (arm \in [Slots -> Orders \cup {NoOrder}])
   /\  (served \in [Orders -> Slots \cup {NoSlot}])
   /\  (credit \in [Orders -> BOOLEAN])
   /\  (tech \in BOOLEAN))

Init ==
  ( (bus = NoOrder)
   /\  (arm = [s \in Slots |-> NoOrder])
   /\  (served = [o \in Orders |-> NoSlot])
   /\  (credit = [o \in Orders |-> FALSE])
   /\  (tech = FALSE))

Pay(o) ==
  ( (~credit[o])
   /\  (served[o] = NoSlot)
   /\  (credit' = [credit EXCEPT ![o] = TRUE])
   /\  (UNCHANGED <<bus, arm, served, tech>>))

TakeBus(o) ==
  ( (bus = NoOrder)
   /\  (credit[o])
   /\  (served[o] = NoSlot)
   /\  (~Armed(o))
   /\  (bus' = o)
   /\  (UNCHANGED <<arm, served, credit, tech>>))

DropBus(o) ==
  ( (bus = o)
   /\  (bus' = NoOrder)
   /\  (UNCHANGED <<arm, served, credit, tech>>))

\* Arming is the last point at which the order is checked against the drop
\* record; the bus goes back in the same step.
ArmSlot(o, s) ==
  ( (bus = o)
   /\  (arm[s] = NoOrder)
   /\  (served[o] = NoSlot)
   /\  (arm' = [arm EXCEPT ![s] = o])
   /\  (bus' = NoOrder)
   /\  (UNCHANGED <<served, credit, tech>>))

Turn(s) ==
  ( (arm[s] # NoOrder)
   /\  (served' = [served EXCEPT ![arm[s]] = s])
   /\  (credit' = [credit EXCEPT ![arm[s]] = FALSE])
   /\  (arm' = [arm EXCEPT ![s] = NoOrder])
   /\  (UNCHANGED <<bus, tech>>))

Disarm(s) ==
  ( (arm[s] # NoOrder)
   /\  (arm' = [arm EXCEPT ![s] = NoOrder])
   /\  (UNCHANGED <<bus, served, credit, tech>>))

Callout ==
  ( (~tech)
   /\  (tech' = TRUE)
   /\  (UNCHANGED <<bus, arm, served, credit>>))

Signoff ==
  ( (tech)
   /\  (tech' = FALSE)
   /\  (UNCHANGED <<bus, arm, served, credit>>))

\* The engineer's key turns a motor with no bus and no arming, but will not
\* touch an order that is already armed somewhere or already served.
KeyTurn(o, s) ==
  ( (tech)
   /\  (credit[o])
   /\  (served[o] = NoSlot)
   /\  (~Armed(o))
   /\  (arm[s] = NoOrder)
   /\  (served' = [served EXCEPT ![o] = s])
   /\  (credit' = [credit EXCEPT ![o] = FALSE])
   /\  (UNCHANGED <<bus, arm, tech>>))

Next ==
  ( (\E o \in Orders : Pay(o))
   \/  (\E o \in Orders : TakeBus(o))
   \/  (\E o \in Orders : DropBus(o))
   \/  (\E o \in Orders, s \in Slots : ArmSlot(o, s))
   \/  (\E s \in Slots : Turn(s))
   \/  (\E s \in Slots : Disarm(s))
   \/  (Callout)
   \/  (Signoff)
   \/  (\E o \in Orders, s \in Slots : KeyTurn(o, s)))

Spec == Init /\ [][Next]_vars

\* Intent: a motor is only ever armed for an order that has had nothing
\* dropped for it yet. Since a drop is what writes the record, no order can
\* have product dropped for it twice.
ArmedOnlyForUnserved ==
  \A s \in Slots : arm[s] # NoOrder => served[arm[s]] = NoSlot

====