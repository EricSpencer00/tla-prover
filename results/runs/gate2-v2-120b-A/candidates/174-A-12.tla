---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
   Node,               \* Set of node identifiers
   SlushLoopProcess,   \* Set of loop process identifiers (one per node)
   SlushQueryProcess,  \* Set of query process identifiers (one per node)
   HostMapping,        \* Set of triples: <<proc, "loop"/"query", node>>
   SlushIterationCount,\* Maximum number of iterations each loop process performs
   SampleSetSize,      \* Number of peers sampled in each round
   PickFlipThreshold,  \* Minimum number of matching replies needed to adopt a color
   NoColor,            \* Symbol representing the uncolored state
   NoMessage           \* Symbol representing the absence of a message (used in model checking)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
LoopProc   == { p \in SlushLoopProcess : 
                \E n \in Node : <<p, "loop", n>> \in HostMapping }
QueryProc  == { p \in SlushQueryProcess : 
                \E n \in Node : <<p, "query", n>> \in HostMapping }
Colors     == {"Red", "Blue", NoColor}
MsgTypes   == {"query", "reply", "term"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
   color,          \* [n \in Node |-> color of node n]
   msgs,           \* Set of in‑flight messages
   pc,             \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> pc value]
   sampleSet,      \* [lp \in SlushLoopProcess |-> set of sampled query processes]
   iterCount       \* [lp \in SlushLoopProcess |-> number of completed iterations]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Message record; each message carries its type and relevant fields.
Msg == [type : {"query", "reply", "term"},
        src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
        dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
        color : {"Red", "Blue", NoColor}]

\* The set of all possible messages (used only for type checking)
AllMsgs == { <<t, s, d, c>> : 
               t \in MsgTypes,
               s \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
               d \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
               c \in Colors }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
 /\ color = [n \in Node |-> NoColor]
 /\ msgs  = {}
 /\ pc    = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 
               IF proc = "client" THEN "AssignColor"
               ELSE IF proc \in LoopProc THEN "WaitForColor"
               ELSE "ReplyLoop"]
 /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
 /\ iterCount = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Client assigns a color to an uncolored node
ClientAssign ==
 /\ pc["client"] = "AssignColor"
 /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ LET chosenColor \in {"Red","Blue"} IN
           /\ color' = [color EXCEPT ![n] = chosenColor]
           /\ pc'    = [pc EXCEPT !["client"] = "AssignColor"]
           /\ UNCHANGED <<msgs, sampleSet, iterCount>>
 /\ UNCHANGED <<color, pc, msgs, sampleSet, iterCount>>

\* 2. Loop process waits until its node has a color
LoopWaitForColor(lp) ==
 /\ pc[lp] = "WaitForColor"
 /\ \E n \in Node :
        /\ <<lp, "loop", n>> \in HostMapping
        /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![lp] = "Sample"]
        /\ UNCHANGED <<color, msgs, sampleSet, iterCount>>

\* 3. Loop process initiates a sampling round
LoopSample(lp) ==
 /\ pc[lp] = "Sample"
 /\ iterCount[lp] < SlushIterationCount
 /\ \E n \in Node :
        /\ <<lp, "loop", n>> \in HostMapping
        /\ \E peers \subseteq QueryProc :
               /\ peers # {}
               /\ Cardinality(peers) = SampleSetSize
               /\ LET curColor == color[n] IN
                  /\ msgs' = msgs \cup { [type |-> "query",
                                         src  |-> lp,
                                         dst  |-> p,
                                         color|-> curColor] : p \in peers }
                  /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
                  /\ pc' = [pc EXCEPT ![lp] = "Collect"]
                  /\ UNCHANGED <<color, iterCount>>
 /\ UNCHANGED <<color, iterCount, sampleSet, pc, msgs>>

\* 4. Query process handles a query message
QueryHandle(qp) ==
 /\ pc[qp] = "ReplyLoop"
 /\ \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst = qp
        /\ \E n \in Node :
               /\ <<qp, "query", n>> \in HostMapping
               /\ LET newColor ==
                       IF color[n] = NoColor THEN m.color ELSE color[n] IN
                  /\ color' = [color EXCEPT ![n] = newColor]
                  /\ msgs' = (msgs \ {m}) \cup { [type |-> "reply",
                                                 src  |-> qp,
                                                 dst  |-> m.src,
                                                 color|-> newColor] }
                  /\ UNCHANGED <<pc, sampleSet, iterCount>>
 /\ UNCHANGED <<pc, sampleSet, iterCount, color, msgs>>

\* 5. Loop process collects replies and possibly flips its node's color
LoopCollect(lp) ==
 /\ pc[lp] = "Collect"
 /\ \E n \in Node :
        /\ <<lp, "loop", n>> \in HostMapping
        /\ \E replies \subseteq msgs :
               /\ \A r \in replies : r.type = "reply" /\ r.dst = lp /\ r.src \in sampleSet[lp]
               /\ Cardinality(replies) = SampleSetSize
               /\ LET red  == Cardinality({ r \in replies : r.color = "Red" })
                      blue == Cardinality({ r \in replies : r.color = "Blue" })
                      cur   == color[n] IN
                  /\ IF red >= PickFlipThreshold THEN newColor = "Red"
                     ELSE IF blue >= PickFlipThreshold THEN newColor = "Blue"
                     ELSE newColor = cur
               /\ color' = [color EXCEPT ![n] = newColor]
               /\ msgs' = msgs \ replies
               /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
               /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
               /\ IF iterCount'[lp] = SlushIterationCount
                     THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
                     ELSE pc' = [pc EXCEPT ![lp] = "Sample"]
               /\ UNCHANGED <<pc, sampleSet, iterCount>>
 /\ UNCHANGED <<color, msgs, sampleSet, iterCount, pc>>

\* 6. Loop process sends termination message
LoopTerminate(lp) ==
 /\ pc[lp] = "Terminate"
 /\ \E n \in Node :
        /\ <<lp, "loop", n>> \in HostMapping
        /\ msgs' = msgs \cup { [type |-> "term",
                                src  |-> lp,
                                dst  |-> "client",
                                color|-> NoColor] }
        /\ pc' = [pc EXCEPT ![lp] = "Done"]
        /\ UNCHANGED <<color, sampleSet, iterCount>>
 /\ UNCHANGED <<color, sampleSet, iterCount, pc, msgs>>

\* 7. Query process exits when a termination message has been observed
QueryExit(qp) ==
 /\ pc[qp] = "ReplyLoop"
 /\ \E m \in msgs :
        /\ m.type = "term"
        /\ m.dst = "client"
        /\ pc' = [pc EXCEPT ![qp] = "Done"]
        /\ msgs' = msgs \ {m}
 /\ UNCHANGED <<color, sampleSet, iterCount, pc, msgs>>

\* 8. Client process finishes when all loop processes are done
ClientDone ==
 /\ pc["client"] = "AssignColor"
 /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
 /\ pc' = [pc EXCEPT !["client"] = "Done"]
 /\ UNCHANGED <<color, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
 \/ \E lp \in SlushLoopProcess : LoopWaitForColor(lp)
 \/ \E lp \in SlushLoopProcess : LoopSample(lp)
 \/ \E qp \in SlushQueryProcess : QueryHandle(qp)
 \/ \E lp \in SlushLoopProcess : LoopCollect(lp)
 \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
 \/ \E qp \in SlushQueryProcess : QueryExit(qp)
 \/ ClientAssign
 \/ ClientDone
 \/ \E lp \in SlushLoopProcess : 
        /\ pc[lp] = "Done"
        /\ UNCHANGED <<color, msgs, pc, sampleSet, iterCount>>
 \/ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "Done"
        /\ UNCHANGED <<color, msgs, pc, sampleSet, iterCount>>
 \/ pc["client"] = "Done"
        /\ UNCHANGED <<color, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (required by the cfg)
\* ----------------------------------------------------------------------
TypeInvariant ==
 /\ color \in [Node -> Colors]
 /\ msgs \subseteq AllMsgs
 /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> 
             {"AssignColor","WaitForColor","Sample","Collect",
              "Terminate","ReplyLoop","Done"} ]
 /\ sampleSet \in [SlushLoopProcess -> SUBSET QueryProc]
 /\ iterCount \in [SlushLoopProcess -> Nat]

====