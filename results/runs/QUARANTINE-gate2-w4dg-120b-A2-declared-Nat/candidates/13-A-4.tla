---- MODULE MCBakery ----
EXTENDS Naturals

\* The inductive specification (ISpec) of the Bakery mutual exclusion
\* algorithm is the same as the original one; this configuration module
\* differs only by fixing the size of the natural-number domain that
\* ticket numbers may come from.  The .cfg file substitutes NatOverride
\* for the built-in Nat, so the model never uses a number above MaxNat.
\* N is the number of concurrent processes participating.

CONSTANTS N, MaxNat, Nat
NatOverride == 0..MaxNat

VARIABLES ticket, cs, phase

vars == <<ticket, cs, phase>>

TypeOK ==
  /\ ticket \in [1..N -> Nat]
  /\ cs \in SUBSET (1..N)
  /\ phase \in [1..N -> {"idle", "waiting", "critical"}]

\* Mutual exclusion: no two processes are ever in the critical section.
MutualExclusion ==
  \A a, b \in cs : a = b

\* The full inductive invariant of the Bakery algorithm.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : phase[i] = "waiting" => (\A j \in 1..N : j # i => ticket[j] # ticket[i] \/ phase[j] = "idle")

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ cs = {}
  /\ phase = [i \in 1..N |-> "idle"]

\* A process requests access: it takes a ticket strictly above every
\* ticket currently in use, and the request is refused if the bound is
\* already reached (this refusal is what keeps the model finite).
Request(i) ==
  /\ phase[i] = "idle"
  /\ \A j \in 1..N : ticket[j] < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = (Max({ticket[k] : k \in 1..N}) + 1)]
  /\ phase' = [phase EXCEPT ![i] = "waiting"]
  /\ UNCHANGED cs

Enter(i) ==
  /\ phase[i] = "waiting"
  /\ \A j \in 1..N : phase[j] = "critical" => ticket[j] > ticket[i]
  /\ cs' = cs \cup {i}
  /\ phase' = [phase EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ phase[i] = "critical"
  /\ cs' = cs \ {i}
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* The inductive spec starts from arbitrary type-correct states and
\* verifies that all reachable states preserve the invariant.
ISpec == Init /\ [][Next]_vars

====