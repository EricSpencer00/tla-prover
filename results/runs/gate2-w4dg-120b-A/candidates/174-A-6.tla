---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

SlushQueryFor(p) == CHOOSE pr \in SlushQueryProcess : <<p, pr>> \in HostMapping

VARIABLES assignment, msgs, pc, sample, iterations
vars == <<assignment, msgs, pc, sample, iterations>>

LoopStep == [proc: SlushLoopProcess, state: {"waitingColor", "collecting", "done"}]
QueryStep == [proc: SlushQueryProcess, state: {"replyLoop", "done"}]
ReqStep == [state: {"ready", "consumed"}]
MsgState == [from: SlushLoopProcess, to: SlushQueryProcess, kind: {"query", "reply", "terminate"}, c: {"b1", "b2", NoColor}]

RECURSIVE CountOv(_, _)
CountOv(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF f[x] THEN 1 + CountOv(f, S \ {x}) ELSE CountOv(f, S \ {x})

Init ==
  /\ assignment = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [lp \in SlushLoopProcess |-> [proc |-> lp, state |-> "waitingColor"]]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iterations = [lp \in SlushLoopProcess |-> 0]
  /\ req == [state |-> "ready"]

PickLoopProcess(n) == CHOOSE p \in SlushLoopProcess : <<p, n>> \in HostMapping

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p].proc = p
       /\ assignment[PickLoopProcess(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = [proc |-> p, state |-> "collecting"]]
  /\ UNCHANGED <<assignment, msgs, sample, iterations>>

QuerySampleSet(p) ==
  /\ pc[p].state = "collecting"
  /\ iterations[p] < SlushIterationCount
  /\ sample[p] = {}
  /\ \E S \subseteq (SlushQueryProcess \ {SlushQueryFor(p)}) :
       /\ Cardinality(S) = SampleSetSize
       /\ sample' = [sample EXCEPT ![p] = S]
  /\ msgs' = msgs \cup
       {[from |-> p, to |-> q, kind |-> "query", c |-> assignment[PickLoopProcess(p)]] : q \in sample[p]}
  /\ UNCHANGED <<assignment, pc, iterations>>

RespondToQuery(msg) ==
  /\ msg.kind = "query"
  /\ \E q \in SlushQueryProcess :
       /\ msg.to = q
       /\ assignment' = [n \in Node |-> IF <<q, n>> \in HostMapping /\ assignment[n] = NoColor
                                          THEN msg.c ELSE assignment[n]]
       /\ msgs' = (msgs \ {msg}) \cup
          {[from |-> msg.from, to |-> q, kind |-> "reply", c |-> assignment[PickLoopProcess(q)]]}
  /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies(p) ==
  /\ pc[p].state = "collecting"
  /\ \E replies \in [SlushQueryProcess -> {"b1", "b2", NoColor}] :
       /\ replies = [q \in SlushQueryProcess |-> CHOOSE r \in msgs :
                       /\ r.kind = "reply"
                       /\ r.from = p
                       /\ r.to = q
                       /\ r.c] /\ assignment' = [n \in Node |-> CHOOSE k \in {"b1", "b2"} :
                                                   IF CountOv(\x \in sample[p] : replies[x] = k, sample[p])
                                                     >= PickFlipThreshold THEN k ELSE assignment[n]]
  /\ msgs' = {msg \in msgs : ~(msg.kind = "reply" /\ msg.from = p)}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
  /\ pc' = [pc EXCEPT ![p] = [proc |-> p, state |-> IF iterations[p] + 1 = SlushIterationCount
                                          THEN "done" ELSE "waitingColor"]]

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p].state = "done"
       /\ msgs' = msgs \cup {[from |-> p, to |-> p, kind |-> "terminate", c |-> NoColor]}
       /\ pc' = [pc EXCEPT ![p] = [proc |-> p, state |-> "done"]]
  /\ UNCHANGED <<assignment, sample, iterations>>

QueryExit ==
  /\ \A p \in SlushLoopProcess : pc[p].state = "done"
  /\ \A q \in SlushQueryProcess : req.state = "ready" =>
       /\ req' = [state |-> "consumed"]
       /\ pc' = [pc EXCEPT ![q] = [proc |-> q, state |-> "done"]]
  /\ UNCHANGED <<assignment, msgs, sample, iterations>>

ClientAssign ==
  /\ req.state = "ready"
  /\ \E n \in Node :
       /\ assignment[n] = NoColor
       /\ \E c \in {"b1", "b2"} : assignment' = [assignment EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, iterations, req>>

Next ==
  \/ RequireColor
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ \E msg \in msgs : RespondToQuery(msg)
  \/ \E p \in SlushLoopProcess : TallyReplies(p)
  \/ LoopTermination
  \/ QueryExit
  \/ ClientAssign

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssign)
        /\ \A p \in SlushLoopProcess : WF_vars(QuerySampleSet(p))
        /\ \A p \in SlushLoopProcess : WF_vars(TallyReplies(p))

TypeInvariant ==
  /\ assignment \in [Node -> {"b1", "b2", NoColor}]
  /\ msgs \subseteq MsgState
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> [proc: SlushLoopProcess \cup SlushQueryProcess, state: {"waitingColor", "collecting", "done", "replyLoop", "ready", "consumed"}]]
  /\ ITERATIONS \in 0 .. SlushIterationCount
====