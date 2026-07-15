---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants (to be supplied in the .cfg)                                 *)
(***************************************************************************)
CONSTANTS
    Node,               \* The set of node identifiers
    SlushLoopProcess,   \* The set of loop process identifiers
    SlushQueryProcess,  \* The set of query process identifiers
    HostMapping,        \* Set of triples <<proc, type, node>> linking processes to nodes
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample each iteration
    PickFlipThreshold,  \* Threshold of replies needed to flip to a color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no in‑flight message"

(***************************************************************************)
(*  Derived sets                                                          *)
(***************************************************************************)
LoopProcs   == { p \in SlushLoopProcess : 
                \E n \in Node : <<p, "loop", n>> \in HostMapping }

QueryProcs  == { p \in SlushQueryProcess : 
                \E n \in Node : <<p, "query", n>> \in HostMapping }

NodeOf   (p) == 
    CASE p \in LoopProcs  -> CHOOSE n \in Node : <<p, "loop", n>> \in HostMapping
    []   p \in QueryProcs -> CHOOSE n \in Node : <<p, "query", n>> \in HostMapping

(***************************************************************************)
(*  Types of messages                                                    *)
(***************************************************************************)
MsgTypes == {"query", "reply", "term"}

Msg == [type : {"query", "reply", "term"},
        src  : SlushLoopProcess \cup SlushQueryProcess,
        dst  : SlushLoopProcess \cup SlushQueryProcess,
        color: NoColor \cup {"c1", "c2"}]

NoMsg == [type |-> "none", src |-> NoMessage, dst |-> NoMessage, color |-> NoColor]

(***************************************************************************)
(*  Variables                                                            *)
(***************************************************************************)
VARIABLES 
    colorMap,      \* Function Node -> NoColor or {"c1","c2"}
    msgs,          \* Set of in‑flight messages
    pc,            \* Program counters: [proc -> stateLabel]
    sampleSet,     \* [loopProc -> SUBSET Node]  (peers sampled this round)
    iterCount      \* [loopProc -> Nat]          (iterations completed)

vars == <<colorMap, msgs, pc, sampleSet, iterCount>>

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)
LoopLabel == {"waitColor", "sendQueries", "waitReplies", "done"}
QueryLabel== {"replyLoop", "done"}
ClientLabel== {"assignColors", "done"}

LoopState(proc) == 
    IF pc[proc] = "sendQueries" THEN [pc EXCEPT ![proc] = "waitReplies"]
    ELSE IF pc[proc] = "waitReplies" THEN [pc EXCEPT ![proc] = "sendQueries"]
    ELSE pc

AllLoopsDone == \A p \in LoopProcs : pc[p] = "done"
AllQueriesDone == \A q \in QueryProcs : pc[q] = "done"

(***************************************************************************)
(*  Initialization                                                       *)
(***************************************************************************)
Init ==
    /\ colorMap = [n \in Node |-> NoColor]
    /\ msgs     = {}
    /\ pc       = [proc \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 
                    IF proc \in LoopProcs THEN "waitColor"
                    ELSE IF proc \in QueryProcs THEN "replyLoop"
                    ELSE "assignColors"]
    /\ sampleSet = [p \in LoopProcs |-> {}]
    /\ iterCount = [p \in LoopProcs |-> 0]

(***************************************************************************)
(*  Actions                                                              *)
(***************************************************************************)
(* 1. Client assigns a color to an uncolored node *)
ClientAssign ==
    /\ pc["client"] = "assignColors"
    /\ \E n \in Node :
          /\ colorMap[n] = NoColor
          /\ LET col == IF RandomChoice({1,2}) = 1 THEN "c1" ELSE "c2" IN
                colorMap' = [colorMap EXCEPT ![n] = col]
          /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>
    /\ IF \A n \in Node : colorMap[n] # NoColor
          THEN pc' = [pc EXCEPT !["client"] = "done"]
          ELSE pc' = pc

(* 2. Loop process waits until its node is colored *)
LoopRequireColor ==
    /\ \E p \in LoopProcs :
          /\ pc[p] = "waitColor"
          /\ colorMap[NodeOf[p]] # NoColor
          /\ pc' = [pc EXCEPT ![p] = "sendQueries"]
    /\ UNCHANGED <<colorMap, msgs, sampleSet, iterCount>>

(* 3. Loop process selects a sample set and sends query messages *)
LoopSendQueries ==
    /\ \E p \in LoopProcs :
          /\ pc[p] = "sendQueries"
          /\ iterCount[p] < SlushIterationCount
          /\ LET peers == Node \ {NodeOf[p]} IN
                sampleSet' = [sampleSet EXCEPT ![p] = 
                                CHOOSE s \subseteq peers : Cardinality(s) = SampleSetSize]
          /\ msgs' = msgs \cup {
                [type |-> "query",
                 src  |-> p,
                 dst  |-> q,
                 color|-> colorMap[NodeOf[p]] ] :
                 q \in SlushQueryProcess :
                 NodeOf[q] \in sampleSet'[p] }
          /\ pc' = [pc EXCEPT ![p] = "waitReplies"]
    /\ UNCHANGED <<colorMap, iterCount>>

(* 4. Query process responds to a query *)
QueryReply ==
    /\ \E qp \in QueryProcs :
          /\ \E m \in msgs :
                /\ m.type = "query"
                /\ m.dst = qp
                /\ LET n == NodeOf[qp] IN
                     /\ IF colorMap[n] = NoColor
                           THEN colorMap' = [colorMap EXCEPT ![n] = m.color]
                           ELSE colorMap' = colorMap
                /\ msgs' = (msgs \ {m}) \cup {
                        [type |-> "reply",
                         src  |-> qp,
                         dst  |-> m.src,
                         color|-> colorMap'[n] ] }
                /\ UNCHANGED <<pc, sampleSet, iterCount>>
    /\ UNCHANGED <<pc, sampleSet, iterCount>>

(* 5. Loop process tallies replies and possibly flips its node's color *)
LoopTallyAndFlip ==
    /\ \E p \in LoopProcs :
          /\ pc[p] = "waitReplies"
          /\ \A q \in SlushQueryProcess :
                 NodeOf[q] \in sampleSet[p] => 
                 \E r \in msgs :
                        /\ r.type = "reply"
                        /\ r.dst = p
                        /\ r.src = q
          /\ LET replies == { r \in msgs :
                                 r.type = "reply" /\ r.dst = p } IN
                /\ LET cnt(color) == Cardinality({ r \in replies : r.color = color }) IN
                /\ IF cnt("c1") >= PickFlipThreshold \/ cnt("c2") >= PickFlipThreshold
                        THEN 
                            LET newCol == IF cnt("c1") >= PickFlipThreshold THEN "c1" ELSE "c2" IN
                            colorMap' = [colorMap EXCEPT ![NodeOf[p]] = newCol]
                        ELSE colorMap' = colorMap
          /\ msgs' = msgs \ { r \in replies : TRUE } \cup {}
          /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
          /\ IF iterCount[p] + 1 = SlushIterationCount
                THEN pc' = [pc EXCEPT ![p] = "done"]
                ELSE pc' = [pc EXCEPT ![p] = "sendQueries"]
          /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ UNCHANGED <<pc, colorMap, msgs, sampleSet, iterCount>>  \* (variables already updated)

(* 6. Query processes exit when all loops are done *)
QueryExit ==
    /\ AllLoopsDone
    /\ \E qp \in QueryProcs :
          /\ pc[qp] = "replyLoop"
          /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<colorMap, msgs, sampleSet, iterCount>>

(* 7. No‑op stutter step to allow deadlock‑free model *)
Stutter ==
    UNCHANGED vars

Next ==
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopSendQueries
    \/ QueryReply
    \/ LoopTallyAndFlip
    \/ QueryExit
    \/ Stutter

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Invariant (type safety)                                               *)
(***************************************************************************)
TypeInvariant ==
    /\ \A n \in Node : colorMap[n] \in NoColor \cup {"c1","c2"}
    /\ \A m \in msgs : 
          /\ m.type \in MsgTypes
          /\ m.src \in SlushLoopProcess \cup SlushQueryProcess
          /\ m.dst \in SlushLoopProcess \cup SlushQueryProcess
          /\ m.color \in NoColor \cup {"c1","c2"}

=============================================================================