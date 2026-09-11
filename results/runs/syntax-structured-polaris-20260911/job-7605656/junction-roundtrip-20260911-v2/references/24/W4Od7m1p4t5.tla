---- MODULE W4Od7m1p4t5 ----
EXTENDS Integers
CONSTANTS NumCranes, Cap
Cranes == 0 .. (NumCranes - 1)

VARIABLES token, buffer, ready, overrides
vars == <<token, buffer, ready, overrides>>

TypeOK ==
    ( (token \in Cranes)
     /\  (buffer \in 0 .. Cap)
     /\  (ready \in [Cranes -> BOOLEAN])
     /\  (overrides \in Nat))

Init ==
    ( (token = 0)
     /\  (buffer = 0)
     /\  (ready = [c \in Cranes |-> FALSE])
     /\  (overrides = 0))

FlagReady(c) ==
    ( (~ready[c])
     /\  (ready' = [ready EXCEPT ![c] = TRUE])
     /\  (UNCHANGED <<token, buffer, overrides>>))

Deposit(c) ==
    ( (token = c)
     /\  (ready[c])
     /\  (buffer < Cap)
     /\  (buffer' = buffer + 1)
     /\  (ready' = [ready EXCEPT ![c] = FALSE])
     /\  (UNCHANGED <<token, overrides>>))

Haul ==
    ( (buffer > 0)
     /\  (buffer' = buffer - 1)
     /\  (UNCHANGED <<token, ready, overrides>>))

Advance ==
    ( (token' = (token + 1) % NumCranes)
     /\  (UNCHANGED <<buffer, ready, overrides>>))

Override(c) ==
    ( (token' = c)
     /\  (overrides' = overrides + 1)
     /\  (UNCHANGED <<buffer, ready>>))

Next ==
    ( (\E c \in Cranes : FlagReady(c))
     \/  (\E c \in Cranes : Deposit(c))
     \/  (Haul)
     \/  (Advance)
     \/  (\E c \in Cranes : Override(c)))

Spec == Init /\ [][Next]_vars

WithinCapacity == buffer <= Cap

OverrideBound == overrides <= 3
====