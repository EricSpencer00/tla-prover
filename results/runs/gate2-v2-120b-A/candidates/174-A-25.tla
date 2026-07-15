---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples [node |-> n, loop |-> l, query |-> q]
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the peer sample each iteration
    PickFlipThreshold,  \* Minimum count of a color in replies to trigger a flip
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no message" (used for init)

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
NodeCount == Cardinality(Node)

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Color == {"Red", "Blue"}

ColorOrNo == Color \cup {NoColor}

MsgType == {"query", "reply", "term"}

Msg == [type : MsgType,
        src  : SlushLoopProcess \cup SlushQueryProcess,
        dst  : SlushLoopProcess \cup SlushQueryProcess,
        payload : UNION {Color, NoMessage}]

MsgSet == SUBSET Msg

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    nodeColor,    \* [node -> ColorOrNo]
    msgs,         \* Set of in‑flight messages
    loopPC,       \* [loopProc -> {"waitColor", "sample", "awaitReplies", "done"}]
    queryPC,      \* [queryProc -> {"replyLoop", "exit"}]
    sampleSet,    \* [loopProc -> SUBSET Node]   (peers sampled this round)
    iterCount     \* [loopProc -> Nat]           (iterations completed)

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
HostNode(l) == 
    CHOOSE n \in Node : 
        \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

HostQuery(p) == 
    CHOOSE q \in SlushQueryProcess :
        \E n \in Node : <<n, p, q>> \in HostMapping

LoopOfNode(n) == 
    CHOOSE l \in SlushLoopProcess :
        \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

QueryOfNode(n) == 
    CHOOSE q \in SlushQueryProcess :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

OtherNodes(n) == Node \ {n}

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ loopPC = [lp \in SlushLoopProcess |-> "waitColor"]
    /\ queryPC = [qp \in SlushQueryProcess |-> "replyLoop"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(*--- Client assigns a color to an uncolored node ---*)
ClientAssign ==
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = 
                 IF RandomChoice = 0 THEN "Red" ELSE "Blue"]
    /\ UNCHANGED <<msgs, loopPC, queryPC, sampleSet, iterCount>>
    /\ ~\E n \in Node : nodeColor[n] = NoColor   \* keep the quantifier in the same line

(* The above uses a deterministic placeholder RandomChoice; we model it as a nondeterministic choice: *)
RandomChoice == CHOOSE i \in {0,1}

ClientAssign ==
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = 
                 IF RandomChoice = 0 THEN "Red" ELSE "Blue"]
    /\ UNCHANGED <<msgs, loopPC, queryPC, sampleSet, iterCount>>

(*--- Loop process waits until its node has a color ---*)
RequireColor(lp) ==
    LET n == HostNode(lp) IN
    /\ nodeColor[n] # NoColor
    /\ loopPC' = [loopPC EXCEPT ![lp] = "sample"]
    /\ UNCHANGED <<nodeColor, msgs, queryPC, sampleSet, iterCount>>

(*--- Loop process selects a sample of peers and sends query messages ---*)
SendQueries(lp) ==
    LET n == HostNode(lp) IN
    /\ loopPC[lp] = "sample"
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = 
          CHOOSE s \in SUBSET OtherNodes(n) : Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup 
        { [type |-> "query",
           src  |-> lp,
           dst  |-> QueryOfNode(p),
           payload |-> nodeColor[n]] : p \in sampleSet'[lp] }
    /\ loopPC' = [loopPC EXCEPT ![lp] = "awaitReplies"]
    /\ UNCHANGED <<nodeColor, queryPC, iterCount>>

(*--- Query process receives a query, possibly adopts the color, and replies ---*)
HandleQuery(qp) ==
    /\ queryPC[qp] = "replyLoop"
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = qp
          /\ LET n == HostNode(LoopOfNode(HostNode(lp))) == 
                 HostNode(LoopOfNode(HostNode(lp))) IN
             n \in Node
          /\ nodeColor' = 
                IF nodeColor[HostNode(LoopOfNode(HostNode(lp)))] = NoColor
                THEN [nodeColor EXCEPT ![HostNode(LoopOfNode(HostNode(lp)))] = m.payload]
                ELSE nodeColor
          /\ msgs' = (msgs \ {m}) \cup 
                { [type |-> "reply",
                   src  |-> qp,
                   dst  |-> m.src,
                   payload |-> nodeColor[HostNode(LoopOfNode(HostNode(lp)))]] }
          /\ UNCHANGED <<loopPC, queryPC, sampleSet, iterCount>>

(* The above uses a complex expression to locate the node associated with the loop that sent the query.
   A simpler approach: we can retrieve the node by reverse mapping from qp to its host node. *)

(* Helper to map a query process to its host node *)
QueryNode(q) == 
    CHOOSE n \in Node :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

LoopNode(l) == HostNode(l)

HandleQuery(qp) ==
    /\ queryPC[qp] = "replyLoop"
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = qp
          /\ node = QueryNode(qp)
          /\ nodeColor' = 
                IF nodeColor[node] = NoColor
                THEN [nodeColor EXCEPT ![node] = m.payload]
                ELSE nodeColor
          /\ msgs' = (msgs \ {m}) \cup 
                { [type |-> "reply",
                   src  |-> qp,
                   dst  |-> m.src,
                   payload |-> nodeColor[node]] }
          /\ UNCHANGED <<loopPC, queryPC, sampleSet, iterCount>>

(*--- Loop process tallies replies, possibly flips its node's color, and proceeds ---*)
ProcessReplies(lp) ==
    LET n == HostNode(lp) IN
    /\ loopPC[lp] = "awaitReplies"
    /\ sampleSet[lp] # {}
    /\ \A p \in sampleSet[lp] :
          \E r \in msgs :
              /\ r.type = "reply"
              /\ r.dst = lp
              /\ r.src = QueryOfNode(p)
    /\ \E redCount, blueCount \in Nat :
          /\ redCount + blueCount = Cardinality(sampleSet[lp])
          /\ \A p \in sampleSet[lp] :
                LET r == CHOOSE r0 \in msgs :
                           r0.type = "reply" /\ r0.dst = lp /\ r0.src = QueryOfNode(p) IN
                (r.payload = "Red" => redCount' = redCount + 1
                 /\ r.payload = "Blue" => blueCount' = blueCount + 1)
          /\ nodeColor' = 
                IF redCount >= PickFlipThreshold
                THEN [nodeColor EXCEPT ![n] = "Red"]
                ELSE IF blueCount >= PickFlipThreshold
                THEN [nodeColor EXCEPT ![n] = "Blue"]
                ELSE nodeColor
          /\ msgs' = msgs \ 
                { r \in msgs : r.type = "reply" /\ r.dst = lp }
          /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
          /\ IF iterCount'[lp] >= SlushIterationCount
                THEN loopPC' = [loopPC EXCEPT ![lp] = "done"]
                ELSE loopPC' = [loopPC EXCEPT ![lp] = "sample"]
          /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ UNCHANGED <<queryPC>>

(*--- Loop termination broadcast (optional, not used for safety) ---*)
BroadcastTerm(lp) ==
    /\ loopPC[lp] = "done"
    /\ msgs' = msgs \cup 
        { [type |-> "term",
           src  |-> lp,
           dst  |-> qp,
           payload |-> NoMessage] : qp \in SlushQueryProcess }
    /\ UNCHANGED <<nodeColor, loopPC, queryPC, sampleSet, iterCount>>

(*--- Query processes exit when every loop has terminated ---*)
ExitQuery(qp) ==
    /\ queryPC[qp] = "replyLoop"
    /\ \A lp \in SlushLoopProcess : loopPC[lp] = "done"
    /\ queryPC' = [queryPC EXCEPT ![qp] = "exit"]
    /\ UNCHANGED <<nodeColor, msgs, loopPC, sampleSet, iterCount>>

(*--- Stuttering step to avoid deadlock after termination ---*)
Stutter ==
    UNCHANGED <<nodeColor, msgs, loopPC, queryPC, sampleSet, iterCount>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : SendQueries(lp)
    \/ \E qp \in SlushQueryProcess : HandleQuery(qp)
    \/ \E lp \in SlushLoopProcess : ProcessReplies(lp)
    \/ \E lp \in SlushLoopProcess : BroadcastTerm(lp)
    \/ \E qp \in SlushQueryProcess : ExitQuery(qp)
    \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<nodeColor, msgs, loopPC, queryPC, sampleSet, iterCount>>

(*--------------------------------------------------------------------
  Type invariant (safety property)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ nodeColor \in [Node -> ColorOrNo]
    /\ msgs \subseteq MsgSet
    /\ loopPC \in [SlushLoopProcess -> {"waitColor", "sample", "awaitReplies", "done"}]
    /\ queryPC \in [SlushQueryProcess -> {"replyLoop", "exit"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

===============