---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush: executable pseudocode for the Slush protocol from the Avalanche   *)
(* whitepaper. Loop processes sample random peers, query them, and adopt a   *)
(* sufficiently popular opinion. Because TLA+ lacks probabilistic reasoning,  *)
(* this spec models only the message flow and the opinion flip; it does not   *)
(* attempt to prove convergence.                                              *)

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

\* Message structure: sender, receiver, a color payload, and a kind field.
Message ==
  [sender : SlushLoopProcess \cup SlushQueryProcess,
   receiver : SlushLoopProcess \cup SlushQueryProcess,
   payload : {NoColor} \cup Node,
   kind : {"query", "reply", "terminate"}]

VARIABLES color, messages, loopPC, queryPC, sample, loopIterations

vars == <<color, messages, loopPC, queryPC, sample, loopIterations>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup Node]
  /\ messages \subseteq Message
  /\ loopPC \in [SlushLoopProcess -> {"requireColor", "querying", "tallying", "done"}]
  /\ queryPC \in [SlushQueryProcess -> {"replyLoop", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ loopPC = [lp \in SlushLoopProcess |-> "requireColor"]
  /\ queryPC = [qp \in SlushQueryProcess |-> "replyLoop"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ loopIterations = [lp \in SlushLoopProcess |-> 0]

QuerySet(lp) == {q \in SlushQueryProcess : Cardinality({q' \in SlushQueryProcess : q' \in sample[lp]}) = SampleSetSize}
ReplySet(lp) == {m \in messages : m.kind = "reply" /\ m.receiver = lp}
ReplyCount(lp, c) == Cardinality({m \in ReplySet(lp) : m.payload = c})

AssignColor(n) ==
  /\ color[n] = NoColor
  /\ \E c \in Node : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, loopPC, queryPC, sample, loopIterations>>

RequireColor(lp) ==
  /\ loopPC[lp] = "requireColor"
  /\ \E n \in Node : <<lp, n>> \in HostMapping /\ color[n] # NoColor
  /\ loopPC' = [loopPC EXCEPT ![lp] = "querying"]
  /\ UNCHANGED <<color, messages, queryPC, sample, loopIterations>>

SendQuery(lp) ==
  /\ loopPC[lp] = "querying"
  /\ \E s \in QuerySet(lp) :
       messages' = messages \cup {[sender |-> lp, receiver |-> s, payload |-> color[CHOOSE n \in Node : <<lp, n>> \in HostMapping], kind |-> "query"]}
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ loopPC' = [loopPC EXCEPT ![lp] = "tallying"]
  /\ UNCHANGED <<color, queryPC, loopIterations>>

RespondQuery(m) ==
  /\ m.kind = "query"
  /\ queryPC[m.receiver] = "replyLoop"
  /\ color' = IF color[CHOOSE n \in Node : <<m.receiver, n>> \in HostMapping] = NoColor
              THEN [color EXCEPT ![CHOOSE n \in Node : <<m.receiver, n>> \in HostMapping] = m.payload]
              ELSE color
  /\ messages' = (messages \ {m}) \cup {[sender |-> m.receiver, receiver |-> m.sender, payload |-> color[CHOOSE n \in Node : <<m.receiver, n>> \in HostMapping], kind |-> "reply"]}
  /\ UNCHANGED <<loopPC, queryPC, sample, loopIterations>>

TallyReplies(lp) ==
  /\ loopPC[lp] = "tallying"
  /\ \A m \in ReplySet(lp) : m.kind = "reply"
  /\ \E c \in Node : ReplyCount(lp, c) >= PickFlipThreshold /\ color' = [color EXCEPT ![CHOOSE n \in Node : <<lp, n>> \in HostMapping] = c]
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ loopIterations' = [loopIterations EXCEPT ![lp] = @ + 1]
  /\ messages' = messages \ ReplySet(lp)
  /\ loopPC' = IF loopIterations[lp] = SlushIterationCount THEN "done" ELSE "querying"
  /\ UNCHANGED <<queryPC>>

SendTerminate(lp) ==
  /\ loopPC[lp] = "done"
  /\ messages' = messages \cup {[sender |-> lp, receiver |-> NoMessage, payload |-> NoMessage, kind |-> "terminate"]}
  /\ UNCHANGED <<color, loopPC, queryPC, sample, loopIterations>>

QueryLoopExit ==
  /\ \A qp \in SlushQueryProcess : queryPC[qp] = "replyLoop"
  /\ \A m \in messages : m.kind = "terminate"
  /\ queryPC' = [qp \in SlushQueryProcess |-> "done"]
  /\ UNCHANGED <<color, messages, loopPC, sample, loopIterations>>

Next ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp)
  \/ \E lp \in SlushLoopProcess : SendQuery(lp)
  \/ \E m \in messages : RespondQuery(m)
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ \E lp \in SlushLoopProcess : SendTerminate(lp)
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

Quiesce ==
  /\ \A lp \in SlushLoopProcess : loopPC[lp] = "done"
  /\ \A qp \in SlushQueryProcess : queryPC[qp] = "done"
  /\ messages = {}

Terminating == <>(Quiesce)

TypeInvariant == TypeOK

====