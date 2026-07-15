---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* ------------------------------------------------------------------------ *)
(*  Constants (to be instantiated in the .cfg file)                         *)
(* ------------------------------------------------------------------------ *)
CONSTANT N, T, F, Values, Bottom

(* ------------------------------------------------------------------------ *)
(*  Derived sets and basic definitions                                      *)
(* ------------------------------------------------------------------------ *)
ProcSet == 1 .. N

Phase == {"bcast1", "wait1", "bcast2", "wait2", "done", "crashed", "choose"}

MsgType == {"phase1", "phase2"}

Message == [type : MsgType,
            sender : ProcSet,
            value : Values,
            est : Values \cup {Bottom}]  \* 'est' is Bottom for phase1 msgs

(* ------------------------------------------------------------------------ *)
(*  State variables                                                         *)
(* ------------------------------------------------------------------------ *)
VARIABLES phase,          \* [proc |-> phase] : each process's control location
          proposed,       \* [proc |-> value]   : each process's initial proposal
          est,            \* [proc |-> value]   : each process's estimated value
          decision,       \* [proc |-> value]   : each process's decision (Bottom if none)
          vi,             \* [proc |-> [sender |-> value]] : local view matrix
          sent,           \* Set of Message
          received,       \* [proc |-> SUBSET Message]
          crashCount      \* Nat, number of crashed processes

vars == << phase, proposed, est, decision, vi, sent, received, crashCount >>

(* ------------------------------------------------------------------------ *)
(*  Initial state                                                          *)
(* ------------------------------------------------------------------------ *)
Init ==
    /\ phase = [p \in ProcSet |-> "bcast1"]
    /\ proposed = [p \in ProcSet |-> CHOOSE v \in Values: TRUE]   \* nondeterministic choice
    /\ est = [p \in ProcSet |-> Bottom]
    /\ decision = [p \in ProcSet |-> Bottom]
    /\ vi = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ sent = {}
    /\ received = [p \in ProcSet |-> {}]
    /\ crashCount = 0

(* ------------------------------------------------------------------------ *)
(*  Actions                                                                *)
(* ------------------------------------------------------------------------ *)

(* Broadcast a phase-1 message *)
BcastPhase1(p) ==
    /\ phase[p] = "bcast1"
    /\ sent' = sent \cup { [type |-> "phase1", sender |-> p,
                           value |-> proposed[p], est |-> Bottom] }
    /\ phase' = [phase EXCEPT ![p] = "wait1"]
    /\ UNCHANGED << proposed, est, decision, vi, received, crashCount >>

(* Receive a phase-1 message *)
RecvPhase1(p, m) ==
    /\ phase[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ vi' = [vi EXCEPT ![p][m.sender] = m.value]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED << phase, proposed, est, decision, crashCount, sent >>

(* Transition from wait1 to broadcast phase2 after receiving N-T distinct msgs *)
ReadyForPhase2(p) ==
    /\ phase[p] = "wait1"
    /\ Cardinality({ m \in received[p] : m.type = "phase1" }) >= N - T
    /\ \A m \in { m \in received[p] : m.type = "phase1" } : m.value # Bottom
    /\ est' = [est EXCEPT ![p] = Max({ vi[p][q] : q \in ProcSet })]
    /\ phase' = [phase EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED << proposed, decision, vi, sent, received, crashCount >>

(* Broadcast a phase-2 message *)
BcastPhase2(p) ==
    /\ phase[p] = "bcast2"
    /\ sent' = sent \cup { [type |-> "phase2", sender |-> p,
                           value |-> proposed[p], est |-> est[p]] }
    /\ phase' = [phase EXCEPT ![p] = "wait2"]
    /\ UNCHANGED << proposed, est, decision, vi, received, crashCount >>

(* Receive a phase-2 message *)
RecvPhase2(p, m) ==
    /\ phase[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ vi' = [vi EXCEPT ![p][m.sender] = m.value]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED << phase, proposed, est, decision, crashCount, sent >>

(* Decide when N-T phase-2 msgs share the same estimated value *)
DecideFromEst(p) ==
    /\ phase[p] = "wait2"
    /\ \E ev \in Values :
          Cardinality({ m \in received[p] : m.type = "phase2" /\ m.est = ev }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = ev]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED << proposed, est, vi, sent, received, crashCount >>

(* Move to choosing state when all N msgs received without a common estimate *)
MoveToChoose(p) ==
    /\ phase[p] = "wait2"
    /\ Cardinality({ m \in received[p] : m.type = "phase2" }) = N
    /\ \A ev \in Values : Cardinality({ m \in received[p] : m.type = "phase2" /\ m.est = ev }) < N - T
    /\ phase' = [phase EXCEPT ![p] = "choose"]
    /\ UNCHANGED << proposed, est, decision, vi, sent, received, crashCount >>

(* Deterministically choose a value from local view and decide *)
ChooseAndDecide(p) ==
    /\ phase[p] = "choose"
    /\ \E v \in Values :
         v = Max({ vi[p][q] : q \in ProcSet })
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED << proposed, est, vi, sent, received, crashCount >>

(* Crash a process (subject to fault bound) *)
Crash(p) ==
    /\ phase[p] # "crashed"
    /\ crashCount < F
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED << proposed, est, decision, vi, sent, received >>

(* ------------------------------------------------------------------------ *)
(*  Next-state relation                                                     *)
(* ------------------------------------------------------------------------ *)
Next ==
    \/ \E p \in ProcSet : BcastPhase1(p)
    \/ \E p \in ProcSet, m \in sent : RecvPhase1(p, m)
    \/ \E p \in ProcSet : ReadyForPhase2(p)
    \/ \E p \in ProcSet : BcastPhase2(p)
    \/ \E p \in ProcSet, m \in sent : RecvPhase2(p, m)
    \/ \E p \in ProcSet : DecideFromEst(p)
    \/ \E p \in ProcSet : MoveToChoose(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

(* ------------------------------------------------------------------------ *)
(*  Specification                                                          *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------ *)
(*  Type correctness invariant (helps TLC)                                 *)
(* ------------------------------------------------------------------------ *)
TypeOK ==
    /\ phase \in [ProcSet -> Phase]
    /\ proposed \in [ProcSet -> Values]
    /\ est \in [ProcSet -> (Values \cup {Bottom})]
    /\ decision \in [ProcSet -> (Values \cup {Bottom})]
    /\ vi \in [ProcSet -> [ProcSet -> (Values \cup {Bottom})]]
    /\ sent \subseteq Message
    /\ received \in [ProcSet -> SUBSET Message]
    /\ crashCount \in Nat
    /\ crashCount <= N

(* ------------------------------------------------------------------------ *)
(*  Safety properties                                                      *)
(* ------------------------------------------------------------------------ *)

(* Validity: any decided value was proposed by some process *)
Validity ==
    \A p \in ProcSet :
        decision[p] # Bottom => decision[p] \in { proposed[q] : q \in ProcSet }

(* Agreement: no two processes decide different values *)
Agreement ==
    \A p, q \in ProcSet :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

=============================================================================