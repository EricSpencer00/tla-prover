---------------------------- MODULE W4Od1m0p3t0 ----------------------------
EXTENDS Naturals

CONSTANTS Flights, Slots, MaxVer

ASSUME MaxVer \in Nat /\ MaxVer >= 1

None == "none"

VARIABLES
    owner,     \* owner[s] = flight that owns slot s, or None
    ver,       \* ver[s] = compare-and-swap version of slot s
    occupant,  \* occupant[s] = flight occupying slot s, or None
    claiming,  \* claiming[s] = flight with an open claim on s, or None
    crashed    \* set of flights that crashed (at most one)

vars == << owner, ver, occupant, claiming, crashed >>

TypeOK ==
    /\ owner \in [Slots -> Flights \cup {None}]
    /\ ver \in [Slots -> 0..MaxVer]
    /\ occupant \in [Slots -> Flights \cup {None}]
    /\ claiming \in [Slots -> Flights \cup {None}]
    /\ crashed \subseteq Flights

Init ==
    /\ owner = [s \in Slots |-> None]
    /\ ver = [s \in Slots |-> 0]
    /\ occupant = [s \in Slots |-> None]
    /\ claiming = [s \in Slots |-> None]
    /\ crashed = {}

\* A live flight opens an optimistic claim on a free, unclaimed slot.
BeginClaim(f, s) ==
    /\ owner[s] = None
    /\ claiming[s] = None
    /\ f \notin crashed
    /\ claiming' = [claiming EXCEPT ![s] = f]
    /\ UNCHANGED << owner, ver, occupant, crashed >>

\* A claim commits by compare-and-swap while the slot is still free.
CommitClaim(f, s) ==
    /\ claiming[s] = f
    /\ owner[s] = None
    /\ owner' = [owner EXCEPT ![s] = f]
    /\ ver' = [ver EXCEPT ![s] = (@ + 1) % (MaxVer + 1)]
    /\ claiming' = [claiming EXCEPT ![s] = None]
    /\ UNCHANGED << occupant, crashed >>

\* A claim aborts because the slot was taken first.
AbortClaim(s) ==
    /\ claiming[s] # None
    /\ owner[s] # None
    /\ claiming' = [claiming EXCEPT ![s] = None]
    /\ UNCHANGED << owner, ver, occupant, crashed >>

\* The named flight occupies its slot.
Occupy(f, s) ==
    /\ owner[s] = f
    /\ occupant[s] = None
    /\ occupant' = [occupant EXCEPT ![s] = f]
    /\ UNCHANGED << owner, ver, claiming, crashed >>

\* A slot is released, clearing its owner and occupant.
Release(s) ==
    /\ occupant[s] # None
    /\ occupant' = [occupant EXCEPT ![s] = None]
    /\ owner' = [owner EXCEPT ![s] = None]
    /\ ver' = [ver EXCEPT ![s] = (@ + 1) % (MaxVer + 1)]
    /\ UNCHANGED << claiming, crashed >>

\* A single flight controller crashes silently, abandoning its claim.
Crash(f) ==
    /\ crashed = {}
    /\ crashed' = {f}
    /\ claiming' = [s \in Slots |-> IF claiming[s] = f THEN None ELSE claiming[s]]
    /\ UNCHANGED << owner, ver, occupant >>

Next ==
    \/ \E f \in Flights, s \in Slots : BeginClaim(f, s)
    \/ \E f \in Flights, s \in Slots : CommitClaim(f, s)
    \/ \E s \in Slots : AbortClaim(s)
    \/ \E f \in Flights, s \in Slots : Occupy(f, s)
    \/ \E s \in Slots : Release(s)
    \/ \E f \in Flights : Crash(f)

Spec == Init /\ [][Next]_vars

\* A flight occupies a slot only while the slot's owner names that same flight.
OccupantOwnsSlot ==
    \A s \in Slots : occupant[s] # None => owner[s] = occupant[s]

=============================================================================