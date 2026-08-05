---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

BASENAME == "Boulanger"

CONSTANTS
    N, MaxNat

VARIABLES
    phase, ticket, pc, waiting, served

vars == <<phase, ticket, pc, waiting, served>>

Phases == {"idle", "trying", "critical"}
MaxTicket == MaxNat - 1

TypeOK ==
    /\ phase \in [1..N -> Phases]
    /\ ticket \in [1..N -> 0..MaxTicket]
    /\ pc \in [0..N]
    /\ waiting \in BOOLEAN

Init == BASENAME

MutualExclusion == BASENAME

Inv == BASENAME

Spec == BASENAME

NatOverride == Nat
====