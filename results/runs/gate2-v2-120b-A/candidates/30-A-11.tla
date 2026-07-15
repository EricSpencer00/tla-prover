---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}

\* ----------------------------------------------------------------------
\* Message type definition
\* ----------------------------------------------------------------------
MsgType == {"phase1", "phase2"}

Message == [type : MsgType,
            sender : Proc,
            proposed : Value,
            estimated : Value]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,            \* control location per process
          proposals,     \* proposed value per process
          localView,     \* N-by-N matrix of received values
          estimate,      \* current estimate per process
          decision,      \* decided value per process
          crashedCount,  \* number of crashed processes
          sent,          \* set of all sent messages
          received       \* set of messages received per process

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Locs == {"broadcast1", "wait1", "broadcast2", "wait2",
         "choosing", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "broadcast1"]
  /\ proposals = [p \in Proc |-> Bottom]            \* will be set by InitPropose
  /\ localView = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ estimate = [p \in Proc |-> Bottom]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MessagesFrom(p) == { msg \in sent : msg.sender = p }

\* Count distinct non-bottom values received from distinct senders in phase 1
Phase1RecvCount(p) ==
  Cardinality({ q \in Proc :
                \E msg \in received[p] :
                  /\ msg.type = "phase1"
                  /\ msg.sender = q
                  /\ msg.proposed = localView[p][q] })

\* Count distinct non-bottom values received from distinct senders in phase 2
Phase2RecvCount(p) ==
  Cardinality({ q \in Proc :
                \E msg \in received[p] :
                  /\ msg.type = "phase2"
                  /\ msg.sender = q
                  /\ msg.estimated = localView[p][q] })

\* Determine if there exists a value appearing in at least N-T phase-2 messages
CommonEstimated(p) ==
  \E v \in Value :
    Cardinality({ q \in Proc :
                  \E msg \in received[p] :
                    /\ msg.type = "phase2"
                    /\ msg.sender = q
                    /\ msg.estimated = v }) >= N - T

\* The value that appears in at least N-T phase-2 messages (if any)
ChosenEstimated(p) ==
  CHOOSE v \in Value :
    Cardinality({ q \in Proc :
                  \E msg \in received[p] :
                    /\ msg.type = "phase2"
                    /\ msg.sender = q
                    /\ msg.estimated = v }) >= N - T

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Propose initial values (nondeterministic, respects Bottom)
InitPropose ==
  /\ \A p \in Proc : proposals[p] \in Values
  /\ UNCHANGED << pc, localView, estimate, decision,
                crashedCount, sent, received >>

\* 2. Broadcast phase‑1 message
Broadcast1(p) ==
  /\ pc[p] = "broadcast1"
  /\ sent' = sent \cup { [type |-> "phase1",
                         sender |-> p,
                         proposed |-> proposals[p],
                         estimated |-> Bottom] }
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << proposals, localView, estimate,
                decision, crashedCount, received >>

\* 3. Receive a phase‑1 message
RecvPhase1(p) ==
  /\ \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \in Proc
        /\ m.sender # p
        /\ m.proposed # Bottom
        /\ m.proposed # localView[p][m.sender]
  /\ \E m \in sent :
        /\ m.type = "phase1"
        /\ m.sender \in Proc
        /\ m.sender # p
        /\ m.proposed # Bottom
        /\ m.proposed # localView[p][m.sender]
        /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ localView' = [localView EXCEPT ![p][m.sender] = m.proposed]
  /\ UNCHANGED << pc, proposals, estimate,
                decision, crashedCount, sent >>

\* 4. After receiving enough phase‑1 messages, compute estimate and broadcast phase‑2
ComputeAndBroadcast2(p) ==
  /\ pc[p] = "wait1"
  /\ Phase1RecvCount(p) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = 
        Max({ localView[p][q] : q \in Proc })]
  /\ sent' = sent \cup { [type |-> "phase2",
                         sender |-> p,
                         proposed |-> proposals[p],
                         estimated |-> estimate[p]] }
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << proposals, localView, decision,
                crashedCount, received >>

\* 5. Receive a phase‑2 message
RecvPhase2(p) ==
  /\ \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \in Proc
        /\ m.sender # p
        /\ m.estimated # Bottom
        /\ m.estimated # localView[p][m.sender]
  /\ \E m \in sent :
        /\ m.type = "phase2"
        /\ m.sender \in Proc
        /\ m.sender # p
        /\ m.estimated # Bottom
        /\ m.estimated # localView[p][m.sender]
        /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ localView' = [localView EXCEPT ![p][m.sender] = m.estimated]
  /\ UNCHANGED << pc, proposals, estimate,
                decision, crashedCount, sent >>

\* 6. Decide when common estimated value seen
Decide(p) ==
  /\ pc[p] = "wait2"
  /\ CommonEstimated(p)
  /\ decision' = [decision EXCEPT ![p] = ChosenEstimated(p)]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << proposals, localView, estimate,
                crashedCount, sent, received >>

\* 7. Move to choosing state when all phase‑2 messages received without agreement
MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality({ m \in received[p] : m.type = "phase2" }) = N
  /\ ~CommonEstimated(p)
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << proposals, localView, estimate,
                decision, crashedCount, sent, received >>

\* 8. Choose deterministically from local view and decide
ChooseAndDecide(p) ==
  /\ pc[p] = "choosing"
  /\ \E v \in Values :
        /\ \E q \in Proc : localView[p][q] = v
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << proposals, localView, estimate,
                crashedCount, sent, received >>

\* 9. Crash a process (if allowed)
Crash(p) ==
  /\ pc[p] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << proposals, localView, estimate,
                decision, sent, received >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : InitPropose
  \/ \E p \in Proc : Broadcast1(p)
  \/ \E p \in Proc : RecvPhase1(p)
  \/ \E p \in Proc : ComputeAndBroadcast2(p)
  \/ \E p \in Proc : RecvPhase2(p)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : ChooseAndDecide(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, proposals, localView, estimate,
                       decision, crashedCount, sent, received>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> Locs]
  /\ proposals \in [Proc -> Values]
  /\ localView \in [Proc -> [Proc -> Value]]
  /\ estimate \in [Proc -> Value]
  /\ decision \in [Proc -> Value]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ received \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    decision[p] # Bottom => decision[p] \in Values

Agreement ==
  \A p, q \in Proc :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Liveness properties (optional, not required as invariants)
\* ----------------------------------------------------------------------
Termination ==
  \A p \in Proc : pc[p] \in {"done", "crashed"}

\* ----------------------------------------------------------------------
\* Theorems (optional, can be omitted)
\* ----------------------------------------------------------------------
\* THEOREM Spec => []TypeOK
\* THEOREM Spec => []Validity
\* THEOREM Spec => []Agreement

====