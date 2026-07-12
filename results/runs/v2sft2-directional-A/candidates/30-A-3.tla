---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N, T, F, Values, Bottom

\* Derived constant: the set of processes
Proc == 1..N

\* Set of all possible messages
Message == {"P1", "P2"} \* Types: Phase 1 or Phase 2

\* State variable declarations
VARIABLES
    pc,                 \* Control location of each process
    view,               \* N-by-N matrix of received values
    prop,               \* Proposed value of each process
    est,                \* Estimated value after Phase 1
    dec,                \* Decision value
    crashed,            \* Set of crashed processes
    sent,               \* Set of messages sent by each process
    recv                \* Set of messages received by each process

\* Control locations
Locs == {"B1", "W1", "B2", "W2", "D", "C", "CR"}  \* B1: broadcast phase1, W1: wait1, B2: broadcast phase2,
                                            \* W2: wait2, D: decided, C: choosing, CR: crashed

\* Helper definitions
BottomVal == Bottom

MaxVal == Max(Values)

\* Initial state
Init ==
    /\ pc = [p \in Proc |-> "B1"]
    /\ view = [i \in Proc |-> [j \in Proc |-> BottomVal]]
    /\ prop \in [p \in Proc |-> Values]
    /\ est = [p \in Proc |-> BottomVal]
    /\ dec = [p \in Proc |-> BottomVal]
    /\ crashed = {}
    /\ sent = [p \in Proc |-> {}]
    /\ recv = [p \in Proc |-> {}]

\* Message type
MessageType(msg) == msg[1]

Receiver(msg) == msg[2]

Value(msg) == msg[3]

\* Phase 1 broadcast: each process sends its proposed value
Phase1Send(p) ==
    /\ pc[p] = "B1"
    /\ LET m == {"P1", p, prop[p]} IN
       /\ sent' = [sent EXCEPT ![p] = @ \cup {m}]
       /\ pc' = [pc EXCEPT ![p] = "W1"]
    /\ UNCHANGED <<view, est, dec, crashed, recv>>

\* Receiving a phase-1 message
Phase1Recv(p, m) ==
    /\ pc[p] \in {"W1", "B2", "W2", "D", "C"}
    /\ m \in sent[Receiver(m)]
    /\ MessageType(m) = "P1"
    /\ LET s == Receiver(m) IN
       /\ view' = [view EXCEPT ![p, s] = Value(m)]
       /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

\* After receiving enough phase-1 messages, compute estimate and move to phase 2 broadcast
Phase1Done(p) ==
    /\ pc[p] = "W1"
    /\ Cardinality({s \in Proc : s \in recv[p] /\ MessageType(s) = "P1"}) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({view[p, s] : s \in Proc /\ view[p, s] \in Values})]
    /\ pc' = [pc EXCEPT ![p] = "B2"]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

\* Phase 2 broadcast
Phase2Send(p) ==
    /\ pc[p] = "B2"
    /\ LET m == {"P2", p, [prop[p], est[p]]} IN
       /\ sent' = [sent EXCEPT ![p] = @ \cup {m}]
       /\ pc' = [pc EXCEPT ![p] = "W2"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

\* Receiving a phase-2 message
Phase2Recv(p, m) ==
    /\ pc[p] \in {"W2", "C"}
    /\ m \in sent[Receiver(m)]
    /\ MessageType(m) = "P2"
    /\ LET s == Receiver(m) IN
       /\ view' = [view EXCEPT ![p, s] = Value(m)[1]]
       /\ est' = [est EXCEPT ![p, s] = Value(m)[2]]
       /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<pc, prop, dec, crashed, sent, view>>

\* After receiving enough identical phase-2 messages, decide
Phase2Decide(p) ==
    /\ pc[p] = "W2"
    /\ \E v \in Values :
         Cardinality({s \in Proc : s \in recv[p] /\ MessageType(s) = "P2" /\ Value(s)[2] = v}) >= N - T
    /\ dec' = [dec EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "D"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* If not enough identical phase-2 messages, move to choosing
Phase2Choose(p) ==
    /\ pc[p] = "W2"
    /\ \A v \in Values :
         Cardinality({s \in Proc : s \in recv[p] /\ MessageType(s) = "P2" /\ Value(s)[2] = v}) < N - T
    /\ pc' = [pc EXCEPT ![p] = "C"]
    /\ UNCHANGED <<view, prop, est, dec, crashed, sent, recv>>

\* Choosing a value deterministically (dequeue from local view)
Choose(p) ==
    /\ pc[p] = "C"
    /\ let vals == {view[p, s] : s \in Proc /\ view[p, s] \in Values} in
       /\ vals \neq {}
    /\ LET v == CHOOSE v \in vals : TRUE IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "D"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* Crashing a process
Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ pc' = [pc EXCEPT ![p] = "CR"]
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* Next-state relation
Next ==
    \/ \E p \in Proc : Phase1Send(p)
    \/ \E p \in Proc, m \in sent[Recvr(m)] : Phase1Recv(p, m)
    \/ \E p \in Proc : Phase1Done(p)
    \/ \E p \in Proc : Phase2Send(p)
    \/ \E p \in Proc, m \in sent[Recvr(m)] : Phase2Recv(p, m)
    \/ \E p \in Proc : Phase2Decide(p)
    \/ \E p \in Proc : Phase2Choose(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)

\* Safety invariants
TypeOK ==
    /\ pc \in [Proc -> Locs]
    /\ view \in [Proc -> [Proc -> Values \cup {BottomVal}]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {BottomVal}]
    /\ dec \in [Proc -> Values \cup {BottomVal}]
    /\ crashed \subseteq Proc
    /\ sent \in [Proc -> SUBSET Message]
    /\ recv \in [Proc -> SUBSET Message]

Validity ==
    \A p \in Proc :
        IF dec[p] \in Values THEN
            \E q \in Proc : prop[q] = dec[p]
        ELSE TRUE

Agreement ==
    \A p, q \in Proc :
        (dec[p] \in Values /\ dec[q] \in Values) => dec[p] = dec[q]

\* Specification
Spec == Init /\ [][Next]_<<pc, view, prop, est, dec, crashed, sent, recv>>

====