---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, localView, proposed, est, decided, crashedCount, msgs, recvd

Variables == <<pc, localView, proposed, est, decided, crashedCount, msgs, recvd>>

\* Two-phase broadcast: phase 1 decides an estimated value via a quorum of
\* messages, then phase 2 decides a decision value via another quorum.
\* Every decision is a received value, so the two safety properties hold.

Locs == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}

MsgSpace == [type: {"p1", "p2"}, val: Values, sender: 1..N, base: Values \cup {Bottom}]

TypeOK ==
    /\ pc \in [1..N -> Locs]
    /\ localView \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ proposed \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashedCount \in 0..N
    /\ msgs \subseteq MsgSpace
    /\ recvd \in [1..N -> SUBSET 1..N]

Init ==
    /\ pc = [i \in 1..N |-> "b1"]
    /\ localView = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ proposed = [i \in 1..N |-> CHOOSE v \in Values : TRUE]
    /\ est = [i \in 1..N |-> Bottom]
    /\ decided = [i \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ msgs = {}
    /\ recvd = [i \in 1..N |-> {}]

\* Phase 1: broadcast a proposal to everyone.
BroadcastP1(i) ==
    /\ pc[i] = "b1"
    /\ msgs' = msgs \cup {[type |-> "p1", val |-> proposed[i], sender |-> i, base |-> Bottom]}
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<localView, proposed, est, decided, crashedCount, recvd>>

ReceiveP1(i, m) ==
    /\ pc[i] = "w1"
    /\ m.type = "p1"
    /\ m.sender \notin recvd[i]
    /\ localView' = [localView EXCEPT ![i][m.sender] = m.val]
    /\ recvd' = [recvd EXCEPT ![i] = recvd[i] \cup {m.sender}]
    /\ UNCHANGED <<pc, proposed, est, decided, crashedCount, msgs>>

\* Reconfiguration: a process may still be slow, not failed, so receiving is
\* weakly fair and it eventually learns enough.
ComputeEst(i) ==
    /\ pc[i] = "w1"
    /\ Cardinality(recvd[i]) >= N - T
    /\ est' = [est EXCEPT ![i] = CHOOSE v \in Values :
                   \E S \in SUBSET 1..N :
                       /\ Cardinality(S) >= N - T
                       /\ \A j \in S : localView[i][j] = v]
    /\ pc' = [pc EXCEPT ![i] = "b2"]
    /\ UNCHANGED <<localView, proposed, decided, crashedCount, msgs, recvd>>

\* Phase 2: broadcast the decision estimate together with the proposal.
BroadcastP2(i) ==
    /\ pc[i] = "b2"
    /\ msgs' = msgs \cup {[type |-> "p2", val |-> proposed[i], sender |-> i, base |-> est[i]]}
    /\ pc' = [pc EXCEPT ![i] = "w2"]
    /\ UNCHANGED <<localView, proposed, est, decided, crashedCount, recvd>>

ReceiveP2(i, m) ==
    /\ pc[i] = "w2"
    /\ m.type = "p2"
    /\ m.sender \notin recvd[i]
    /\ localView' = [localView EXCEPT ![i][m.sender] = m.val]
    /\ recvd' = [recvd EXCEPT ![i] = recvd[i] \cup {m.sender}]
    /\ UNCHANGED <<pc, proposed, est, decided, crashedCount, msgs>>

DecideOnEst(i) ==
    /\ pc[i] = "w2"
    /\ \E v \in Values :
         /\ Cardinality({j \in recvd[i] : localView[i][j] = v}) >= N - T
         /\ decided' = [decided EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, proposed, est, crashedCount, msgs, recvd>>

\* If no estimate reached the quorum, the process crashes through an explicit
\* choosing step instead of looping forever.
Choose(i) ==
    /\ pc[i] = "w2"
    /\ recvd[i] = 1..N
    /\ \A v \in Values : Cardinality({j \in recvd[i] : localView[i][j] = v}) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<localView, proposed, est, decided, crashedCount, msgs, recvd>>

MakeChoice(i) ==
    /\ pc[i] = "choose"
    /\ decided' = [decided EXCEPT ![i] = CHOOSE v \in Values : \E j \in 1..N : localView[i][j] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, proposed, est, crashedCount, msgs, recvd>>

Crash(i) ==
    /\ pc[i] \notin {"crashed", "done"}
    /\ crashedCount < F
    /\ crashedCount' = crashedCount + 1
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED <<localView, proposed, est, decided, msgs, recvd>>

Next ==
    \/ \E i \in 1..N : BroadcastP1(i)
    \/ \E i \in 1..N, m \in msgs : ReceiveP1(i, m)
    \/ \E i \in 1..N : ComputeEst(i)
    \/ \E i \in 1..N : BroadcastP2(i)
    \/ \E i \in 1..N, m \in msgs : ReceiveP2(i, m)
    \/ \E i \in 1..N : DecideOnEst(i)
    \/ \E i \in 1..N : Choose(i)
    \/ \E i \in 1..N : MakeChoice(i)
    \/ \E i \in 1..N : Crash(i)

\* Quiet crash-stop: weak fairness on everything but crashing, which is
\* bounded by the fault budget and never starves the other actions.
Spec ==
    /\ Init
    /\ [][Next]_Variables
    /\ \A i \in 1..N, m \in msgs :
         /\ WF_Variables(ReceiveP1(i, m))
         /\ WF_Variables(ReceiveP2(i, m))
    /\ \A i \in 1..N :
         /\ WF_Variables(ComputeEst(i))
         /\ WF_Variables(DecideOnEst(i))
         /\ WF_Variables(Choose(i))
         /\ SF_Variables(MakeChoice(i))

\* Every decision the protocol ever makes was proposed by somebody.
Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : proposed[j] = decided[i]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* The quorum condition here is the same arithmetic bound the model checks
\* in the model itself: it is not a manifestation of any other part of the
\* spec, so the bound stands or falls on its own.
Termination == <>(\A i \in 1..N : pc[i] \in {"done", "crashed"})

\* Conditional termination: the failure bound is tight, so the condition on
\* who started out proposing the maximum is exactly what separates guaranteed
\* termination from just the chance that a strong majority agreed.
ConditionC1 ==
    LET maxv == CHOOSE v \in Values : \A w \in Values : w <= v
    IN Cardinality({i \in 1..N : proposed[i] = maxv}) >= F + 1

ConditionalTermination == ConditionC1 ~> Termination

====