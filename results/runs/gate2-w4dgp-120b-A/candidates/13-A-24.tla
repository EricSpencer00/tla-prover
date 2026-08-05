---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES ticket, claim, cs, served
vars == <<ticket, claim, cs, served>>

\* The natural numbers are reinterpreted for model checking only. Everything
\* that is defined as Nat in the original Bakery model is now defined over
\* the finite range 0..MaxNat, so the state space stays finite.
Nat == 0..MaxNat

InCS == {i \in 1..N : cs[i] = "in"}
InCS2 == {i \in 1..N : cs[i] = "cs2"}

TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ claim \in [1..N -> Nat]
  /\ cs \in [1..N -> {"idle", "waiting", "in", "cs2"}]
  /\ served \in Nat

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ claim = [i \in 1..N |-> 0]
  /\ cs = [i \in 1..N |-> "idle"]
  /\ served = 0

Bump(n) == IF n < MaxNat THEN n + 1 ELSE n

\* A process acquires a ticket for the critical section.
Take(i) ==
  /\ cs[i] = "idle"
  /\ ticket' = [ticket EXCEPT ![i] = Bump(ticket[i])]
  /\ claim' = [claim EXCEPT ![i] = Bump(claim[i])]
  /\ cs' = [cs EXCEPT ![i] = "waiting"]
  /\ UNCHANGED served

\* A process enters the critical section once its ticket is the smallest
\* of all currently waiting processes' tickets.
Enter(i) ==
  /\ cs[i] = "waiting"
  /\ \A j \in 1..N : (cs[j] = "waiting" => claim[i] <= ticket[j])
  /\ cs' = [cs EXCEPT ![i] = "in"]
  /\ UNCHANGED <<ticket, claim, served>>

\* A process leaves the critical section.
Exit(i) ==
  /\ cs[i] = "in"
  /\ cs' = [cs EXCEPT ![i] = "idle"]
  /\ served' = Bump(served)
  /\ UNCHANGED <<ticket, claim>>

\* A process can be slow without ever being treated as failed: it may sit
\* in its critical section for an arbitrary number of steps before leaving.
Hold(i) ==
  /\ cs[i] = "in"
  /\ UNCHANGED vars

\* A slow process may take the critical section a second time before
\* leaving it for good.
Reenter(i) ==
  /\ cs[i] = "cs2"
  /\ cs' = [cs EXCEPT ![i] = "in"]
  /\ UNCHANGED <<ticket, claim, served>>

\* A slow process leaves the critical section, but into a different
\* state as a bookkeeping step before it can reenter.
ExitToReenter(i) ==
  /\ cs[i] = "in"
  /\ cs' = [cs EXCEPT ![i] = "cs2"]
  /\ UNCHANGED <<ticket, claim, served>>

Next ==
  \/ \E i \in 1..N : Take(i) \/ Enter(i) \/ Exit(i) \/ Hold(i) \/ Reenter(i) \/ ExitToReenter(i)

ISpec == Init /\ [][Next]_vars

MutualExclusion ==
  /\ /\ InCS = {}
     \/ \E i \in 1..N : InCS = {i}
  /\ \A i \in 1..N : (cs[i] = "cs2" => ticket[i] # 0 /\ claim[i] # 0)

Inv ==
  /\ MutualExclusion
  /\ TypeOK
====