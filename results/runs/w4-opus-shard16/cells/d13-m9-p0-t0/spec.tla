-------------------------- MODULE W4Od13m9p0t0 --------------------------
EXTENDS Naturals

CONSTANTS Machines, NoOne, MaxEpoch

VARIABLES
    curEpoch,       \* hub's current epoch
    holder,         \* machine holding the vault grant, or NoOne
    holderEpoch,    \* epoch the current grant was stamped with
    inVault,        \* inVault[m] : is machine m inside the vault?
    crashed         \* set of silently-crashed machines

vars == << curEpoch, holder, holderEpoch, inVault, crashed >>

TypeOK ==
    /\ curEpoch \in 0..MaxEpoch
    /\ holder \in (Machines \cup {NoOne})
    /\ holderEpoch \in 0..MaxEpoch
    /\ inVault \in [Machines -> BOOLEAN]
    /\ crashed \subseteq Machines

Init ==
    /\ curEpoch = 0
    /\ holder = NoOne
    /\ holderEpoch = 0
    /\ inVault = [m \in Machines |-> FALSE]
    /\ crashed = {}

GrantStale == (holder = NoOne) \/ (holderEpoch < curEpoch)

\* Acquire the grant when free or held under a retired epoch.
Acquire(m) ==
    /\ m \notin crashed
    /\ GrantStale
    /\ holder' = m
    /\ holderEpoch' = curEpoch
    /\ UNCHANGED << curEpoch, inVault, crashed >>

\* Only the current-epoch grant holder may enter the vault.
Enter(m) ==
    /\ m \notin crashed
    /\ holder = m
    /\ holderEpoch = curEpoch
    /\ ~inVault[m]
    /\ inVault' = [inVault EXCEPT ![m] = TRUE]
    /\ UNCHANGED << curEpoch, holder, holderEpoch, crashed >>

Exit(m) ==
    /\ m \notin crashed
    /\ inVault[m]
    /\ inVault' = [inVault EXCEPT ![m] = FALSE]
    /\ holder' = NoOne
    /\ UNCHANGED << curEpoch, holderEpoch, crashed >>

\* Reconfigure to recover; the barrier forces everyone out of the vault.
Reconfigure ==
    /\ curEpoch < MaxEpoch
    /\ curEpoch' = curEpoch + 1
    /\ inVault' = [m \in Machines |-> FALSE]
    /\ UNCHANGED << holder, holderEpoch, crashed >>

Crash(m) ==
    /\ m \notin crashed
    /\ crashed' = crashed \cup {m}
    /\ UNCHANGED << curEpoch, holder, holderEpoch, inVault >>

Recover(m) ==
    /\ m \in crashed
    /\ crashed' = crashed \ {m}
    /\ UNCHANGED << curEpoch, holder, holderEpoch, inVault >>

Next ==
    \/ \E m \in Machines : Acquire(m)
    \/ \E m \in Machines : Enter(m)
    \/ \E m \in Machines : Exit(m)
    \/ Reconfigure
    \/ \E m \in Machines : Crash(m)
    \/ \E m \in Machines : Recover(m)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: never two machines inside the vault at once.
VaultExclusion ==
    \A m, n \in Machines : (inVault[m] /\ inVault[n]) => (m = n)

=============================================================================
