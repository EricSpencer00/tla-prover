---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Processes: partitioned nondeterministically into correct vs. faulty (Byzantine),
\* with at most T Byzantine. A correct process that received the broadcaster's
\* INIT message sends an ECHO to all, and accepts once it has heard from enough
\* distinct senders -- the Srikanth/Toueg one-round condition. Byzantine processes
\* can inject arbitrary ECHO messages, modeled as "any possible" message.
\* Safety: no correct accept unless some correct started the broadcast.
\* Liveness: a broadcast by correct enough processes eventually reaches all.

\* Identities (phases): broadcast-received (init), not-received, sent echo, accepted.
\* The "sent from one" set below tracks which processes have emitted a message.

VARIABLES correct, faulty, loc, received, sentFrom
vars == <<correct, faulty, loc, received, sentFrom>>

Msg == {"echo"}

InitPhases == {"init", "nobc"}
Locs == {"init", "nobc", "echoed", "done"}

TypeOK ==
  /\ correct \cup faulty = 1..N /\ correct \cap faulty = {}
  /\ loc \in [1..N -> Locs]
  /\ received \in [1..N -> SUBSET (1..N \X Msg)]
  /\ sentFrom \in SUBSET 1..N

Init ==
  /\ N > 3 * T /\ T >= F /\ F >= 0
  /\ \E c \in SUBSET (1..N) :
       /\ Cardinality(c) = N - F
       /\ correct = c
       /\ \E i \in c :
            loc = [j \in 1..N |-> IF j = i THEN "init" ELSE "nobc"]
  /\ faulty = (1..N) \ correct
  /\ received = [j \in 1..N |-> {}]
  /\ sentFrom = {}

InitAlt ==
  /\ N > 3 * T /\ T >= F /\ F >= 0
  /\ \E c \in SUBSET (1..N) :
       /\ Cardinality(c) = N - F
       /\ correct = c
       /\ loc = [j \in 1..N |-> "nobc"]
  /\ faulty = (1..N) \ correct
  /\ received = [j \in 1..N |-> {}]
  /\ sentFrom = {}

\* A correct process may receive any set of new messages from the universe of
\* possible messages: those sent by correct processes, plus any Byzantine messages.
Recv(j, m) ==
  /\ j \in correct
  /\ m \subseteq ((sentFrom \ X {Msg}) \cup ((1..N) \ X {Msg}))
  /\ m # {}
  /\ m \not\subseteq received[j]
  /\ received' = [received EXCEPT ![j] = @ \cup m]
  /\ UNCHANGED <<correct, faulty, loc, sentFrom>>

BRecv(j) == Recv(j, m)
  where m \in {
      {p}
      : p \in ((sentFrom \ X {Msg}) \cup ((1..N) \ X {Msg}))
    }

Bcast(j) ==
  /\ j \in correct
  /\ loc[j] = "init"
  /\ sentFrom' = sentFrom \cup {j}
  /\ loc' = [loc EXCEPT ![j] = "echoed"]
  /\ UNCHANGED <<correct, faulty, received>>

Echoed(j, k) ==
  /\ j \in correct
  /\ loc[j] \in {"nobc", "init"}
  /\ Cardinality({p \in received[j] : p[2] = "echo"}) >= N - 2 * T
  /\ Cardinality({p \in received[j] : p[2] = "echo"}) < N - T
  /\ k = Cardinality({p \in received[j] : p[2] = "echo"})
  /\ sentFrom' = sentFrom \cup {j}
  /\ loc' = [loc EXCEPT ![j] = "echoed"]
  /\ UNCHANGED <<correct, faulty, received>>

Acceptable(j) ==
  Cardinality({p \in received[j] : p[2] = "echo"}) >= N - T

Echoed2(j) ==
  /\ Echoed(j, k)
  /\ Acceptable(j)
  /\ loc' = [loc EXCEPT ![j] = "done"]
  /\ UNCHANGED <<correct, faulty, received, sentFrom>>

Done(j) ==
  /\ j \in correct
  /\ loc[j] = "echoed"
  /\ Acceptable(j)
  /\ loc' = [loc EXCEPT ![j] = "done"]
  /\ UNCHANGED <<correct, faulty, received, sentFrom>>

Next == (\E j \in 1..N : BRecv(j)) \/ (\E j \in correct : Bcast(j))
        \/ (\E j \in correct : Echoed2(j)) \/ (\E j \in correct : Done(j))

Spec == Init /\ [][Next]_vars /\ WF_vars(\E j \in 1..N : BRecv(j))
CorrLtl == (loc["init"] = "init") ~> (loc["init"] = "done")
RelayLtl == (\E j \in correct : loc[j] = "done")
              ~> (\A j \in correct : loc[j] = "done")

\* Safety: without a correct initiator (no broadcast), no correct ever accepts.
UnforgLtl == (\A j \in correct : loc[j] = "nobc") ~> (\A j \in correct : loc[j] # "done")
FCConstraints == N > 3 * T /\ T >= F /\ F >= 0
====