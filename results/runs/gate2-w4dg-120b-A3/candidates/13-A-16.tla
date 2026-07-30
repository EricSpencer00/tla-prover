---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES entering, cs, ticket, nextTicket
vars == <<entering, cs, ticket, nextTicket>>

\* The original Bakery shared queues use the infinite Nat type for tickets and
\* the base specification starts from the fully-initialised state.  Here we
\* replace Nat globally with a finite range (0..MaxNat) so the state space
\* stays bounded, and we use the inductive spec ISpec instead of InitSpec.
\* The NatOverride line below replaces the Nat operator from Naturals with
\* a finite version; keep EXTENDS Naturals and do NOT declare Nat yourself.
NatOverride == (Nat \cap (0 .. MaxNat))

Init ==
  /\ entering = [p \in 0 .. (N - 1) |-> FALSE]
  /\ cs = [p \in 0 .. (N - 1) |-> FALSE]
  /\ ticket = [p \in 0 .. (N - 1) |-> 0]
  /\ nextTicket = 0

\* The ticket number stays within the finite bound of MaxNat.
Request(p) ==
  /\ ~entering[p]
  /\ ~cs[p]
  /\ entering' = [entering EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = IF nextTicket < MaxNat THEN nextTicket ELSE nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED cs

Enter(p) ==
  /\ entering[p]
  /\ \A q \in 0 .. (N - 1) : ~cs[q] /\ (ticket[q] = 0 \/ ticket[q] > ticket[p])
  /\ entering' = [entering EXCEPT ![p] = FALSE]
  /\ cs' = [cs EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ cs[p]
  /\ cs' = [cs EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<entering, nextTicket>>

Next == \E p \in 0 .. (N - 1) : Request(p) \/ Enter(p) \/ Exit(p)

ISpec == \A p \in 0 .. (N - 1) : Request(p) \/ Enter(p) \/ Exit(p)

MutualExclusion ==
  \A p, q \in 0 .. (N - 1) : (cs[p] /\ cs[q]) => p = q

TypeOK ==
  /\ entering \in [0 .. (N - 1) -> BOOLEAN]
  /\ cs \in [0 .. (N - 1) -> BOOLEAN]
  /\ ticket \in [0 .. (N - 1) -> 0 .. MaxNat]
  /\ nextTicket \in 0 .. MaxNat

Inv == MutualExclusion /\ TypeOK

Spec == ISpec

====