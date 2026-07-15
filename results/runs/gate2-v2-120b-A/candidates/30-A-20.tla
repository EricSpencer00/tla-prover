---------------------------- MODULE cbc_max ----------------------------
EXTENDS Naturals, Sequences, TLC

(* --algorithm (not used) placeholder to silence warnings --*)

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types and derived constants
\* ----------------------------------------------------------------------
Proc == 1..N
MsgType == {"P1", "P2"}
Value == Values
Estim == Values

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,                 \* control location of each process
    local,              \* N-by-N matrix of observed values
    prop,               \* proposed value of each process
    est,                \* estimated value after phase 1
    dec,                \* decision value (Bottom means no decision yet)
    crashed,            \* set of crashed processes
    sent,               \* set of all messages ever sent
    recv                \* map: process -> set of messages it has received

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Msg == [type : MsgType,
        sender : Proc,
        value : Value,
        est : Estim \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* All processes are distinct and within 1..N
ProcSet == {1,2,3,4,5,6,7,8,9,10} \* dummy; actual bound given by constant N

\* Maximum of a non‑empty set of totally ordered values
Max(S) == IF S = {} THEN Bottom ELSE CHOOSE x \in S : 
          \A y \in S : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "BroadcastP1"]
    /\ local = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ prop \in [p \in Proc |-> Value]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastP1(p) ==
    /\ pc[p] = "BroadcastP1"
    /\ sent' = sent \cup { [type |-> "P1",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "WaitP1"]
    /\ UNCHANGED <<local, prop, est, dec, crashed, recv>>

RecvP1(p) ==
    /\ pc[p] \in {"WaitP1", "BroadcastP2"}   \* can receive while waiting or before broadcasting P2
    /\ \E m \in sent :
          /\ m.type = "P1"
          /\ m.sender \notin crashed
          /\ m.sender \notin recv[p]         \* not received before
          /\ local' = [local EXCEPT ![p][m.sender] = m.value]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

ComputeEst(p) ==
    /\ pc[p] = "WaitP1"
    /\ Cardinality({ s \in Proc : local[p][s] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ local[p][s] : s \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "BroadcastP2"]
    /\ UNCHANGED <<local, prop, dec, crashed, sent, recv>>

BroadcastP2(p) ==
    /\ pc[p] = "BroadcastP2"
    /\ sent' = sent \cup { [type |-> "P2",
                           sender |-> p,
                           value |-> prop[p],
                           est |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "WaitP2"]
    /\ UNCHANGED <<local, prop, est, dec, crashed, recv>>

RecvP2(p) ==
    /\ pc[p] \in {"WaitP2", "Choosing"}
    /\ \E m \in sent :
          /\ m.type = "P2"
          /\ m.sender \notin crashed
          /\ m.sender \notin recv[p]
          /\ local' = [local EXCEPT ![p][m.sender] = m.value]
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

DecideFromEst(p) ==
    /\ pc[p] = "WaitP2"
    /\ \E e \in Estim :
          /\ Cardinality({ m \in recv[p] : m.type = "P2" /\ m.est = e }) >= N - T
    /\ LET e == CHOOSE v \in Estim :
                Cardinality({ m \in recv[p] : m.type = "P2" /\ m.est = v }) >= N - T
       IN
          /\ dec' = [dec EXCEPT ![p] = e]
          /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<local, prop, est, crashed, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "WaitP2"
    /\ Cardinality({ m \in recv[p] : m.type = "P2" }) = N
    /\ \A e \in Estim :
          Cardinality({ m \in recv[p] : m.type = "P2" /\ m.est = e }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<local, prop, est, dec, crashed, sent, recv>>

ChooseAndDecide(p) ==
    /\ pc[p] = "Choosing"
    /\ \E v \in Values :
          /\ v \in { local[p][q] : q \in Proc }
    /\ LET v == CHOOSE w \in Values :
                w \in { local[p][q] : q \in Proc }
       IN
          /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<local, prop, est, crashed, sent, recv>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "Crashed"]
    /\ UNCHANGED <<local, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastP1(p)
    \/ \E p \in Proc : RecvP1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastP2(p)
    \/ \E p \in Proc : RecvP2(p)
    \/ \E p \in Proc : DecideFromEst(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, local, prop, est, dec, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness (helps TLC, not part of the required invariants)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"BroadcastP1","WaitP1","BroadcastP2","WaitP2",
                       "Done","Crashed","Choosing"}]
    /\ local \in [Proc -> [Proc -> (Value \cup {Bottom})]]
    /\ prop \in [Proc -> Value]
    /\ est \in [Proc -> (Estim \cup {Bottom})]
    /\ dec \in [Proc -> (Value \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

=============================================================================