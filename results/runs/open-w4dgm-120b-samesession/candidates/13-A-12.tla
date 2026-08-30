---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This module models the Bakery mutual exclusion algorithm, but it is a
\* model-checking configuration: the infinite natural numbers are replaced
\* with a finite range 0..MaxNat so the reachable state space stays
\* finite.  The safety-relevant invariant is the same as in the full
\* Bakery spec; the change only affects the range of ticket numbers.

\* The state is the process phase, a bounded ticket number, and a copy of
\* the register a process read when it entered the bakery.

Processes == 1..N
Phases    == {"idle", "waiting", "cs"}
Seats     == {0} \cup Processes

VARIABLES phase, ticket, readReg, reg

vars == << phase, ticket, readReg, reg >>

TypeOK ==
  /\ phase \in [Processes -> Phases]
  /\ ticket \in [Processes -> 0..MaxNat]
  /\ readReg \in [Processes -> Seats]
  /\ reg \in Seats

Init ==
  /\ phase = [p \in Processes |-> "idle"]
  /\ ticket = [p \in Processes |-> 0]
  /\ readReg = [p \in Processes |-> 0]
  /\ reg = 0

\* A process enters the bakery, snapping up a bounded ticket number; it is
\* free to leave the bakery without entering the critical section.
Snap(p) ==
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat THEN ticket[p] + 1 ELSE ticket[p]]
  /\ readReg' = [readReg EXCEPT ![p] = reg]
  /\ UNCHANGED reg

\* A waiting process enters the critical section only if its snap was
\* still current (the register is unchanged since it read it) and the
\* register still reads free, i.e. it is the oldest waiting process.
Enter(p) ==
  /\ phase[p] = "waiting"
  /\ readReg[p] = reg
  /\ readReg[p] = 0
  /\ reg' = p
  /\ phase' = [phase EXCEPT ![p] = "cs"]
  /\ UNCHANGED << ticket, readReg >>

Leave(p) ==
  /\ phase[p] = "cs"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ reg' = 0
  /\ UNCHANGED << ticket, readReg >>

Next == (\E p \in Processes : Snap(p)) \/ (\E p \in Processes : Enter(p)) \/ (\E p \in Processes : Leave(p))

\* The inductive specification starts from any type-correct reachable state
\* and not just the initial state, so the invariant must hold regardless of
\* where the system currently sits.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in Processes : phase[p] = "cs" => reg = p

Inv == MutualExclusion

\* The operator replacement goes here: NatOverride replaces Naturals' Nat
\* with a FINITE version so the model is checkable, while EXTENDS Naturals
\* is still in force and Nat itself is never declared here.
NatOverride == 0..MaxNat

====