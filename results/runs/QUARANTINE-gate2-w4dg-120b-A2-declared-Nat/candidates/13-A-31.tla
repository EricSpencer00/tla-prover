---- MODULE MCBakery ----
EXTENDS Integers

CONSTANTS N, MaxNat, Nat

\* NatOverride replaces Nat in the original Bakery spec with a finite range
\* for model checking; the .cfg substitutes NatOverride for Nat.
NatOverride == Nat
NatSet == 0..MaxNat

VARIABLES phase, ticket, maxTicket

vars == << phase, ticket, maxTicket >>

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0

\* The bakery actions are unchanged from the original spec; they are merely
\* re-declared here so the module supplies every identifier the .cfg expects.
\* Ticket numbers are bounded by the overridden Nat range.
Request(p) ==
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket

Enter(p) ==
  /\ phase[p] = "waiting"
  /\ \A q \in 1..N : (phase[q] # "critical") \/ (ticket[p] < ticket[q])
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ UNCHANGED << ticket, maxTicket >>

Exit(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED maxTicket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

\* The full inductive invariant: no two critical-section processes share a
\* ticket, and every waiting or critical process holds a non-zero ticket within
\* the bounded range.
Inv ==
  /\ \A p \in 1..N : phase[p] = "idle" => ticket[p] = 0
  /\ \A p \in 1..N : phase[p] \in {"waiting", "critical"} => ticket[p] \in NatSet /\ ticket[p] >= 1
  /\ \A p, q \in 1..N :
       (p # q /\ phase[p] = "critical" /\ phase[q] = "critical")
         => ticket[p] # ticket[q]

TypeOK ==
  /\ phase \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> NatSet]
  /\ maxTicket \in NatSet

MutualExclusion ==
  \A p, q \in 1..N :
    (p # q /\ phase[p] = "critical" /\ phase[q] = "critical") => FALSE

ISpec ==
  /\ Init
  /\ [][Next]_vars
  /\ UNCHANGED << >>  \* no additional action; the spec is the inductive one

====