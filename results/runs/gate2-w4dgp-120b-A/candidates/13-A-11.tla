---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES x, cs, ticket, nextTicket

vars == <<x, cs, ticket, nextTicket>>

TypeOK ==
    /\ x \in 0 .. (N - 1)
    /\ cs \in BOOLEAN
    /\ ticket \in 0 .. MaxNat
    /\ nextTicket \in 0 .. MaxNat

Inv ==
    /\ cs = (x \in 0 .. (N - 1))
    /\ (cs /\ ticket > 0 => ticket <= nextTicket)

Init ==
    /\ x = 0
    /\ cs = FALSE
    /\ ticket = 0
    /\ nextTicket = 0

Acquire ==
    /\ cs = FALSE
    /\ cs' = TRUE
    /\ x' = (x + 1) % N
    /\ ticket' = nextTicket + 1
    /\ nextTicket' = nextTicket + 1

Exit ==
    /\ cs = TRUE
    /\ cs' = FALSE
    /\ ticket' = 0
    /\ UNCHANGED <<x, nextTicket>>

Next == Acquire \/ Exit

ISpec == Init /\ [][Next]_vars

MutualExclusion == TRUE

NatOverride == Nat

====