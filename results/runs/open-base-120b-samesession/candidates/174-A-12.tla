---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Constants (to be supplied in the .cfg file)                           *)
(* ----------------------------------------------------------------------- *)
CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop process must run
    SampleSetSize,       \* Size of the random sample each iteration
    PickFlipThreshold,   \* Threshold for flipping the node's color
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Special placeholder message (unused but required)

(***************************************************************************)
(*  Derived sets and helper functions                                      *)
(* ----------------------------------------------------------------------- *)

\* Colors used by the protocol
Color == {"Red", "Blue"}

\* All process identifiers (loop, query and the client)
Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* Message types ---------------------------------------------------------
QueryMsg == [type    : {"Query"},
             from    : SlushLoopProcess,
             to      : SlushQueryProcess,
             color   : Color]

ReplyMsg == [type    : {"Reply"},
             from    : SlushQueryProcess,
             to      : SlushLoopProcess,
             color   : Color]

TermMsg  == [type    : {"Term"},
             from    : SlushLoopProcess,
             to      : SlushQueryProcess]

Message == QueryMsg \cup ReplyMsg \cup TermMsg

\* Helper to retrieve the node that hosts a given loop process
HostNode(p) == 
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

\* Helper to retrieve the query process that belongs to a given node
HostQuery(q) ==
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* The set of query processes that correspond to a set of nodes
QueryProcsOfNodes(S) ==
    { q \in SlushQueryProcess :
        \E n \in S : \E l \in SlushLoopProcess :
            <<n, l, q>> \in HostMapping }

\* The node that a query process belongs to
NodeOfQuery(q) ==
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* The node that a loop process belongs to (same as HostNode)
NodeOfLoop(l) == HostNode(l)

(***************************************************************************)
(*  Variables                                                              *)
(* ----------------------------------------------------------------------- *)

VARIABLES
    colorMap,   \* [Node -> (Color \cup {NoColor})]
    msgs,       \* SUBSET Message
    sample,     \* [SlushLoopProcess -> SUBSET Node]   (current sample set)
    iter,       \* [SlushLoopProcess -> Nat]            (iterations done)
    pc          \* [Proc -> {"Assign", "Done",
                            "WaitColor", "Sample", "WaitReplies",
                            "Update", "Terminate",
                            "ReplyLoop"}]

vars == <<colorMap, msgs, sample, iter, pc>>

(***************************************************************************)
(*  Initialization                                                         *)
(* ----------------------------------------------------------------------- *)

Init ==
    /\ colorMap = [n \in Node |-> NoColor]
    /\ msgs      = {}
    /\ sample    = [lp \in SlushLoopProcess |-> {}]
    /\ iter      = [lp \in SlushLoopProcess |-> 0]
    /\ pc        = [p \in Proc |
                      IF p = "Client" THEN "Assign"
                      ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                      ELSE "ReplyLoop"]

(***************************************************************************)
(*  Actions                                                                *)
(* ----------------------------------------------------------------------- *)

\* -------------------------------------------------------------
\* 1. Client assigns a random color to an uncolored node
\* -------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "Assign"
    /\ \E n \in Node :
         /\ colorMap[n] = NoColor
         /\ \E c \in Color :
                /\ colorMap' = [colorMap EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, sample, iter, pc>>
                /\ pc' = [pc EXCEPT !["Client"] = "Assign"]
    /\ UNCHANGED <<colorMap, msgs, sample, iter, pc>>  \* guarded by the above existential

\* -------------------------------------------------------------
\* 2. Loop process waits until its node has a color
\* -------------------------------------------------------------
LoopRequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "WaitColor"
         /\ colorMap[NodeOfLoop(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<colorMap, msgs, sample, iter>>

\* -------------------------------------------------------------
\* 3. Loop process samples peers and sends query messages
\* -------------------------------------------------------------
LoopSample ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "Sample"
         /\ LET myNode   == NodeOfLoop(lp)
                other    == Node \ {myNode}
                s        == CHOOSE S \in SUBSET other : Cardinality(S) = SampleSetSize
                qProcs   == QueryProcsOfNodes(s)
                qMsgs    == { [type |-> "Query",
                               from |-> lp,
                               to   |-> q,
                               color|-> IF colorMap[myNode] = NoColor THEN NoColor
                                        ELSE colorMap[myNode] ] : q \in qProcs }
          IN
             /\ sample' = [sample EXCEPT ![lp] = s]
             /\ msgs'   = msgs \cup qMsgs
             /\ pc'     = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<colorMap, iter>>

\* -------------------------------------------------------------
\* 4. Query process receives a query, possibly adopts the color,
\*    and replies
\* -------------------------------------------------------------
QueryRespond ==
    /\ \E q \in SlushQueryProcess :
         /\ \E m \in msgs :
                /\ m.type = "Query"
                /\ m.to   = q
                /\ LET n    == NodeOfQuery(q)
                       newC == IF colorMap[n] = NoColor THEN m.color ELSE colorMap[n]
                       reply == [type |-> "Reply",
                                 from |-> q,
                                 to   |-> m.from,
                                 color|-> newC]
                 IN
                    /\ colorMap' = [colorMap EXCEPT ![n] = newC]
                    /\ msgs'      = (msgs \ {m}) \cup {reply}
    /\ UNCHANGED <<sample, iter, pc>>

\* -------------------------------------------------------------
\* 5. Loop process tallies replies; may flip its node's color,
\*    increments iteration counter, and either continues or
\*    terminates
\* -------------------------------------------------------------
LoopTally ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "WaitReplies"
         /\ LET s       == sample[lp]                     \* nodes sampled this round
                qProcs  == QueryProcsOfNodes(s)
                replies == { r \in msgs :
                               r.type = "Reply" /\ r.to = lp /\ r.from \in qProcs }
                /\ Cardinality(replies) = SampleSetSize
                colors  == { r.color : r \in replies }
                redCnt  == Cardinality({ r \in replies : r.color = "Red" })
                blueCnt == Cardinality({ r \in replies : r.color = "Blue" })
                \* Determine the dominant color (if any) that meets the threshold
                newColor == IF redCnt >= PickFlipThreshold THEN "Red"
                           ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                           ELSE colorMap[NodeOfLoop(lp)]
                hostN   == NodeOfLoop(lp)
                msgs'   == msgs \ replies                     \* remove the processed replies
                iter'   == [iter EXCEPT ![lp] = @ + 1]
                sample' == [sample EXCEPT ![lp] = {}]
                pc'     == IF iter'[lp] < SlushIterationCount
                           THEN [pc EXCEPT ![lp] = "Sample"]
                           ELSE [pc EXCEPT ![lp] = "Terminate"]
                colorMap' == [colorMap EXCEPT ![hostN] = newColor]
         IN
            /\ UNCHANGED <<>>
    /\ UNCHANGED <<>>

\* -------------------------------------------------------------
\* 6. Loop process sends termination messages to all query processes
\* -------------------------------------------------------------
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "Terminate"
         /\ LET termMsgs == { [type |-> "Term",
                               from |-> lp,
                               to   |-> q] :
                               q \in SlushQueryProcess }
         IN
            /\ msgs' = msgs \cup termMsgs
            /\ pc'   = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<colorMap, sample, iter>>

\* -------------------------------------------------------------
\* 7. Query processes exit when all loop processes are Done and
\*    they have received their termination messages
\* -------------------------------------------------------------
QueryTerminate ==
    /\ \E q \in SlushQueryProcess :
         /\ pc[q] = "ReplyLoop"
         /\ /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
            /\ \A m \in msgs : m.type = "Term" /\ m.to = q
         /\ pc' = [pc EXCEPT ![q] = "Done"]
         /\ msgs' = msgs \ { m \in msgs : m.type = "Term" /\ m.to = q }
    /\ UNCHANGED <<colorMap, sample, iter>>

\* -------------------------------------------------------------
\* 8. Stuttering step (allows the system to remain in a state)
\* -------------------------------------------------------------
Stutter ==
    /\ UNCHANGED vars

Next ==
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryTerminate
    \/ Stutter

(***************************************************************************)
(*  Specification                                                          *)
(* ----------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant                                                         *)
(* ----------------------------------------------------------------------- *)

TypeInvariant ==
    /\ colorMap \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message

(***************************************************************************)
(*  Exported identifiers                                                   *)
(* ----------------------------------------------------------------------- *)

\* The configuration file expects the following names
THEOREM SpecIsSpec == Spec
INVARIANT TypeInvariant

====