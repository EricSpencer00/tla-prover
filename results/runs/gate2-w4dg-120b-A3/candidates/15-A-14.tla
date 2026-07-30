---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME /\ N \in Nat /\ T \in Nat /\ F \in Nat
       /\ N > 3 * T
       /\ T >= F

Processes == 1 .. N
Msgs == {"ECHO"}

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs
vars == << correct, faulty, pc, recvMsgs, sentMsgs >>

InitStates == {"bcast", "noBcast"}
Locs == {"no", "rcvd", "sent", "done"}

Init == /\ correct = {1 .. (N - F)}
        /\ faulty = {N - F + 1 .. N}
        /\ pc \in [Processes -> Locs]
        /\ \A p \in Processes : pc[p] \in InitStates
        /\ recvMsgs \in [Processes -> SUBSET [snd : Processes, typ : Msgs]]
        /\ sentMsgs \in SUBSET [snd : Processes, typ : Msgs]

\* A restricted start: no correct process received the INIT message.
QuietInit == /\ pc = [p \in Processes |-> "noBcast"]
             /\ UNCHANGED << correct, faulty, pc, recvMsgs, sentMsgs >>

\* Correct processes receive whatever is available, from correct and
\* Byzantine senders alike; this is the only nondeterministic receipt step.
Receive(p) == /\ p \in correct
              /\ pc[p] \in {"noBcast", "bcast"}
              /\ \E m \in [Processes -> SUBSET [snd : Processes, typ : Msgs]] :
                    /\ \A q \in Processes : m[q] \subseteq sentMsgs \cup [snd : Processes, typ : Msgs]
                    /\ recvMsgs' = [recvMsgs EXCEPT ![p] = m[p]]
              /\ UNCHANGED << correct, faulty, pc, sentMsgs >>

\* A process with the INIT message accepts and ECHOs immediately.
ActInit(p) == /\ p \in correct
              /\ pc[p] = "bcast"
              /\ pc' = [pc EXCEPT ![p] = "done"]
              /\ sentMsgs' = sentMsgs \cup {[snd |-> p, typ |-> "ECHO"]}
              /\ UNCHANGED << correct, faulty, recvMsgs >>

\* Early acceptance: enough ECHOs to send, but not yet to accept.
ActBeforeQuorum(p) == /\ p \in correct
                      /\ pc[p] = "noBcast"
                      /\ Cardinality({m \in recvMsgs[p] : m.typ = "ECHO"}) >= (N - 2 * T)
                      /\ Cardinality({m \in recvMsgs[p] : m.typ = "ECHO"}) < (N - T)
                      /\ pc' = [pc EXCEPT ![p] = "sent"]
                      /\ sentMsgs' = sentMsgs \cup {[snd |-> p, typ |-> "ECHO"]}
                      /\ UNCHANGED << correct, faulty, recvMsgs >>

\* Quorum acceptance: enough ECHOs to accept in the same step.
ActAtQuorum(p) == /\ p \in correct
                  /\ pc[p] = "noBcast"
                  /\ Cardinality({m \in recvMsgs[p] : m.typ = "ECHO"}) >= (N - T)
                  /\ pc' = [pc EXCEPT ![p] = "done"]
                  /\ sentMsgs' = sentMsgs \cup {[snd |-> p, typ |-> "ECHO"]}
                  /\ UNCHANGED << correct, faulty, recvMsgs >>

\* Late acceptance: a process that already sent ECHO now accepts.
ActLate(p) == /\ p \in correct
              /\ pc[p] = "sent"
              /\ Cardinality({m \in recvMsgs[p] : m.typ = "ECHO"}) >= (N - T)
              /\ pc' = [pc EXCEPT ![p] = "done"]
              /\ UNCHANGED << correct, faulty, recvMsgs, sentMsgs >>

Next == \/ QuietInit
        \/ \E p \in Processes :
             Receive(p) \/ ActInit(p) \/ ActBeforeQuorum(p) \/ ActAtQuorum(p) \/ ActLate(p)

\* Weak fairness on the combined receive-and-act steps for each correct process.
Spec == Init /\ [][Next]_vars
        /\ \A p \in Processes :
             TRUE
             /\ (p \in correct) ~> (pc[p] = "done")
             /\ (p \in correct) ~> (pc[p] = "rcvd")
             /\ (p \in correct) ~> (pc[p] = "sent")

TypeOK == /\ correct \subseteq Processes
          /\ faulty \subseteq Processes
          /\ pc \in [Processes -> Locs]
          /\ recvMsgs \in [Processes -> SUBSET [snd : Processes, typ : Msgs]]
          /\ sentMsgs \in SUBSET [snd : Processes, typ : Msgs]

\* No forged acceptance: if no correct process broadcasts, none accepts.
FCConstraints == (pc = [p \in Processes |-> "bcast"]) ~> (pc = [p \in Processes |-> "done"])

CorrLtl == (pc = [p \in Processes |-> "bcast"]) ~> (pc = [p \in Processes |-> "done"])
RelayLtl == (\E p \in Processes : pc[p] = "done") ~> (pc = [p \in Processes |-> "done"])
UnforgLtl == (pc = [p \in Processes |-> "noBcast"]) ~> (pc = [p \in Processes |-> "no"])

====