---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<process, "host", node>>
    SlushIterationCount,\* Number of iterations each loop process must run
    SampleSetSize,      \* Size of the peer sample chosen each iteration
    PickFlipThreshold,  \* Threshold of replies needed to adopt a color
    NoColor,            \* Special value representing "uncolored"
    NoMessage           \* Special value representing "no message" (used for termination)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Colors == {"Red", "Blue"}

Nodes == Node
LoopProcs == SlushLoopProcess
QueryProcs == SlushQueryProcess

(*-----------------------------------------------------------------
  Helper functions
-----------------------------------------------------------------*)
HostOf(p) == 
    IF p \in LoopProcs THEN 
        CHOOSE n \in Nodes: <<p, "host", n>> \in HostMapping
    ELSE IF p \in QueryProcs THEN
        CHOOSE n \in Nodes: <<p, "host", n>> \in HostMapping
    ELSE NoColor

(*-----------------------------------------------------------------
  Message representation
-----------------------------------------------------------------*)
Msg == {"Query", "QueryReply", "Terminate"}

Vars ==
    [ color      |-> [n \in Nodes |-> NoColor],
      msgs       |-> {},               \* Set of in‑flight messages
      pcLoop     |-> [lp \in LoopProcs |-> "RequireColor"],
      pcQuery    |-> [qp \in QueryProcs |-> "ReplyLoop"],
      sampleSet  |-> [lp \in LoopProcs |-> {}],
      iterCount  |-> [lp \in LoopProcs |-> 0],
      clientPc   |-> "AssignColor" ]

(*-----------------------------------------------------------------
  Message constructors
-----------------------------------------------------------------*)
QueryMsg(lp, qp) == <<lp, qp, "Query", color[HostOf(lp)]>>
ReplyMsg(qp, lp) == <<qp, lp, "QueryReply", color[HostOf(qp)]>>
TerminateMsg(lp) == <<lp, "Terminate">>

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ color = [n \in Nodes |-> NoColor]
    /\ msgs = {}
    /\ pcLoop = [lp \in LoopProcs |-> "RequireColor"]
    /\ pcQuery = [qp \in QueryProcs |-> "ReplyLoop"]
    /\ sampleSet = [lp \in LoopProcs |-> {}]
    /\ iterCount = [lp \in LoopProcs |-> 0]
    /\ clientPc = "AssignColor"

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

(* --- Client action: assign a random color to an uncolored node --- *)
ClientAssign ==
    /\ clientPc = "AssignColor"
    /\ \E n \in Nodes :
         /\ color[n] = NoColor
         /\ LET c == CHOOSE col \in Colors : TRUE IN
            /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pcLoop, pcQuery, sampleSet, iterCount>>
    /\ clientPc' = IF \A n \in Nodes : color[n] # NoColor THEN "Done" ELSE "AssignColor"

(* --- Loop process waits until its host node has a color --- *)
RequireColor(lp) ==
    /\ pcLoop[lp] = "RequireColor"
    /\ color[HostOf(lp)] # NoColor
    /\ pcLoop' = [pcLoop EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, pcQuery, sampleSet, iterCount, clientPc>>

(* --- Loop process builds a sample set and sends queries --- *)
QuerySample(lp) ==
    /\ pcLoop[lp] = "Sample"
    /\ iterCount[lp] < SlushIterationCount
    /\ \E peers \in SUBSET QueryProcs :
         /\ peers # {}
         /\ Cardinality(peers) = SampleSetSize
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
         /\ msgs' = msgs \cup { QueryMsg(lp, qp) : qp \in peers }
    /\ pcLoop' = [pcLoop EXCEPT ![lp] = "Collect"]
    /\ UNCHANGED <<color, pcQuery, iterCount, clientPc>>

(* --- Loop process collects replies from all sampled peers --- *)
CollectReplies(lp) ==
    /\ pcLoop[lp] = "Collect"
    /\ \A qp \in sampleSet[lp] :
         \E m \in msgs :
            /\ m = ReplyMsg(qp, lp)
    /\ msgs' = msgs \ { ReplyMsg(qp, lp) : qp \in sampleSet[lp] }
    /\ LET reds   == { qp \in sampleSet[lp] : color[HostOf(qp)] = "Red" }
           blues  == { qp \in sampleSet[lp] : color[HostOf(qp)] = "Blue" } IN
       IF Cardinality(reds) >= PickFlipThreshold THEN
           color' = [color EXCEPT ![HostOf(lp)] = "Red"]
       ELSE IF Cardinality(blues) >= PickFlipThreshold THEN
           color' = [color EXCEPT ![HostOf(lp)] = "Blue"]
       ELSE
           color' = color
    /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ pcLoop' = IF iterCount[lp] + 1 = SlushIterationCount
                 THEN "Terminate"
                 ELSE "Sample"
    /\ UNCHANGED <<pcQuery, clientPc>>

(* --- Loop process sends a termination message --- *)
Terminate(lp) ==
    /\ pcLoop[lp] = "Terminate"
    /\ msgs' = msgs \cup {TerminateMsg(lp)}
    /\ pcLoop' = [pcLoop EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sampleSet, iterCount, pcQuery, clientPc>>

(* --- Query process replies to a query --- *)
ReplyQuery(qp) ==
    /\ pcQuery[qp] = "ReplyLoop"
    /\ \E m \in msgs :
         /\ m = QueryMsg(lp, qp)
         /\ LET sender == lp IN
            /\ color' = IF color[HostOf(qp)] = NoColor
                        THEN [color EXCEPT ![HostOf(qp)] = color[HostOf(sender)]]
                        ELSE color
            /\ msgs' = msgs \ {m} \cup { ReplyMsg(qp, sender) }
    /\ UNCHANGED <<pcLoop, sampleSet, iterCount, clientPc>>

(* --- Query process exits when all loop processes are done --- *)
ExitQuery(qp) ==
    /\ pcQuery[qp] = "ReplyLoop"
    /\ \A lp \in LoopProcs : pcLoop[lp] = "Done"
    /\ pcQuery' = [pcQuery EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, pcLoop, sampleSet, iterCount, clientPc>>

(* --- Stuttering step to keep the model from deadlocking --- *)
Stutter ==
    UNCHANGED <<color, msgs, pcLoop, pcQuery, sampleSet, iterCount, clientPc>>

Next ==
    \/ \E lp \in LoopProcs : RequireColor(lp)
    \/ \E lp \in LoopProcs : QuerySample(lp)
    \/ \E lp \in LoopProcs : CollectReplies(lp)
    \/ \E lp \in LoopProcs : Terminate(lp)
    \/ \E qp \in QueryProcs : ReplyQuery(qp)
    \/ \E qp \in QueryProcs : ExitQuery(qp)
    \/ ClientAssign
    \/ Stutter

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<color, msgs, pcLoop, pcQuery, sampleSet, iterCount, clientPc>>

(*-----------------------------------------------------------------
  Type invariant (the only invariant required by the cfg)
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ \A n \in Nodes : color[n] \in Colors \cup {NoColor}
    /\ \A m \in msgs :
          ( /\ Len(m) = 4 /\ m[3] \in {"Query", "QueryReply"}
             /\ (m[3] = "Query" => m[4] \in Colors \cup {NoColor})
             /\ (m[3] = "QueryReply" => m[4] \in Colors \cup {NoColor}) )
          \/ ( /\ Len(m) = 2 /\ m[2] = "Terminate" )
    /\ pcLoop \in [LoopProcs -> {"RequireColor", "Sample", "Collect", "Terminate", "Done"}]
    /\ pcQuery \in [QueryProcs -> {"ReplyLoop", "Done"}]
    /\ \A lp \in LoopProcs :
          Cardinality(sampleSet[lp]) \in 0..SampleSetSize
    /\ \A lp \in LoopProcs : 0 <= iterCount[lp] <= SlushIterationCount
    /\ clientPc \in {"AssignColor", "Done"}

=============================================================================