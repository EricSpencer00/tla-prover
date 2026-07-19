-------------------------- MODULE W4Od7m8p4t5 --------------------------
EXTENDS Naturals

CONSTANTS Cranes, Stacks, NoOne, Cap

VARIABLES
    coarse,     \* holder of the coarse bay-lock, or NoOne
    fine,       \* fine[s] : holder of stack s's fine-lock, or NoOne
    occupancy,  \* number of containers in the bay
    adminBusy   \* TRUE iff the administrator holds the yard

vars == << coarse, fine, occupancy, adminBusy >>

TypeOK ==
    /\ coarse \in (Cranes \cup {NoOne})
    /\ fine \in [Stacks -> (Cranes \cup {NoOne})]
    /\ occupancy \in 0..Cap
    /\ adminBusy \in BOOLEAN

Init ==
    /\ coarse = NoOne
    /\ fine = [s \in Stacks |-> NoOne]
    /\ occupancy = 0
    /\ adminBusy = FALSE

AcquireCoarse(c) ==
    /\ ~adminBusy
    /\ coarse = NoOne
    /\ coarse' = c
    /\ UNCHANGED << fine, occupancy, adminBusy >>

HoldsNoFine(c) == \A s \in Stacks : fine[s] # c

ReleaseCoarse(c) ==
    /\ coarse = c
    /\ HoldsNoFine(c)
    /\ coarse' = NoOne
    /\ UNCHANGED << fine, occupancy, adminBusy >>

AcquireFine(c, s) ==
    /\ coarse = c
    /\ fine[s] = NoOne
    /\ fine' = [fine EXCEPT ![s] = c]
    /\ UNCHANGED << coarse, occupancy, adminBusy >>

ReleaseFine(c, s) ==
    /\ fine[s] = c
    /\ fine' = [fine EXCEPT ![s] = NoOne]
    /\ UNCHANGED << coarse, occupancy, adminBusy >>

\* Load requires the stack's fine lock and remaining room in the bay.
Load(c, s) ==
    /\ fine[s] = c
    /\ occupancy < Cap
    /\ occupancy' = occupancy + 1
    /\ UNCHANGED << coarse, fine, adminBusy >>

Unload(c, s) ==
    /\ fine[s] = c
    /\ occupancy > 0
    /\ occupancy' = occupancy - 1
    /\ UNCHANGED << coarse, fine, adminBusy >>

\* Admin override: drop all crane locks and take exclusive control.
AdminSeize ==
    /\ ~adminBusy
    /\ adminBusy' = TRUE
    /\ coarse' = NoOne
    /\ fine' = [s \in Stacks |-> NoOne]
    /\ UNCHANGED occupancy

\* While in control the administrator may drain the bay.
AdminDrain ==
    /\ adminBusy
    /\ occupancy' = 0
    /\ UNCHANGED << coarse, fine, adminBusy >>

AdminRelease ==
    /\ adminBusy
    /\ adminBusy' = FALSE
    /\ UNCHANGED << coarse, fine, occupancy >>

Next ==
    \/ \E c \in Cranes : AcquireCoarse(c)
    \/ \E c \in Cranes : ReleaseCoarse(c)
    \/ \E c \in Cranes, s \in Stacks : AcquireFine(c, s)
    \/ \E c \in Cranes, s \in Stacks : ReleaseFine(c, s)
    \/ \E c \in Cranes, s \in Stacks : Load(c, s)
    \/ \E c \in Cranes, s \in Stacks : Unload(c, s)
    \/ AdminSeize
    \/ AdminDrain
    \/ AdminRelease

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the bay is never over-filled.
WithinCapacity == occupancy <= Cap

=============================================================================
