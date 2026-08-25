---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node,                 \* Set of node identifiers
  SlushLoopProcess,     \* Set of loop processes (one per node)
  SlushQueryProcess,    \* Set of query processes (one per node)
  HostMapping,          \* Set of triples <<loop, query, node>>
  SlushIterationCount,  \* Number of iterations each loop process must perform
  SampleSetSize,        \* Size of the peer sample taken each round
  PickFlipThreshold,    \* Threshold for adopting a color
  NoColor,              \* Symbol representing the uncolored state
  NoMessage              \* Symbol used as a placeholder color in termination messages

(* ----------------------------------------------------------------- *)
(*   Basic domain definitions                                         *)
(* ----------------------------------------------------------------- *)

Color == {"Red", "Blue"}                     \* The two possible opinions

Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess),
            dst   : (SlushLoopProcess \cup SlushQueryProcess \cup {"All"}),
            color : (Color \cup {NoMessage})]

(* ----------------------------------------------------------------- *)
(*   Helper functions                                                 *)
(* ----------------------------------------------------------------- *)

HostNode(lp) ==
  CHOOSE n \in Node :
    \E qp \in SlushQueryProcess : <<lp, qp, n>> \in HostMapping

HostNodeFromQuery(qp) ==
  CHOOSE n \in Node :
    \E lp \in SlushLoopProcess : <<lp, qp, n>> \in HostMapping

HostQuery(n) ==
  CHOOSE qp \in SlushQueryProcess :
    \E lp \in SlushLoopProcess : <<lp, qp, n>> \in HostMapping

SampleProcesses(lp) ==
  { HostQuery(n) : n \in sample[lp] }

(* ----------------------------------------------------------------- *)
(*   Variables                                                       *)
(* ----------------------------------------------------------------- *)

VARIABLES
  color,   \* [node \in Node |-> NoColor \/ Color]
  msgs,    \* Set of Message
  pc,      \* Program counter for every process (including the client)
  sample,  \* [lp \in SlushLoopProcess |-> {}]                 current peer sample
  iter     \* [lp \in SlushLoopProcess |-> 0]                  iteration counter

vars == <<color, msgs, pc, sample, iter>>

(* ----------------------------------------------------------------- *)
(*   Initialization                                                   *)
(* ----------------------------------------------------------------- *)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs   = {}
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iter   = [lp \in SlushLoopProcess |-> 0]
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 
            IF p = "Client"          THEN "assign"
            ELSE IF p \in SlushLoopProcess  THEN "waitColor"
            ELSE                               "replyLoop"]

(* ----------------------------------------------------------------- *)
(*   Actions                                                         *)
(* ----------------------------------------------------------------- *)

(* 1. Client assigns a random color to an uncolored node *)
ClientAssign ==
  /\ pc["Client"] = "assign"
  /\ \E n \in Node : color[n] = NoColor
  /\ \E c \in Color :
       /\ color' = [color EXCEPT ![n] = c]
       /\ pc' = [pc EXCEPT !["Client"] =
                 IF \A n2 \in Node : color'[n2] # NoColor
                 THEN "done"
                 ELSE "assign"]
       /\ UNCHANGED <<msgs, sample, iter>>

(* 2. Loop process waits until its host node is colored *)
LoopRequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "waitColor"
       /\ LET n == HostNode(lp) IN color[n] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "sample"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

(* 3. Loop process samples peers and sends query messages *)
LoopSample ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "sample"
       /\ LET n == HostNode(lp) IN
          \E s \subseteq Node \ {n} :
             /\ Cardinality(s) = SampleSetSize
             /\ LET qs == { HostQuery(n2) : n2 \in s } IN
                /\ msgs' = msgs \cup
                     { [type  |-> "query",
                        src   |-> lp,
                        dst   |-> qp,
                        color |-> color[n]] : qp \in qs }
                /\ sample' = [sample EXCEPT ![lp] = s]
                /\ pc' = [pc EXCEPT ![lp] = "waitReplies"]
                /\ UNCHANGED <<color, iter>>
  (* only one loop process takes a step at a time *)

(* 4. Query process receives a query, possibly adopts the color, and replies *)
QueryRespond ==
  /\ \E m \in msgs :
        /\ m.type = "query"
        /\ LET qp == m.dst
               lp == m.src
               n  == HostNodeFromQuery(qp)
               cur == color[n]
               newCol == IF cur = NoColor THEN m.color ELSE cur
        IN
           /\ color' = [color EXCEPT ![n] = newCol]
           /\ msgs' = (msgs \ {m}) \cup
                { [type  |-> "reply",
                   src   |-> qp,
                   dst   |-> lp,
                   color |-> newCol] }
           /\ UNCHANGED <<pc, sample, iter>>

(* 5. Loop process tallies replies, possibly flips its color, and proceeds *)
LoopTally ==
  /\ \E lp \in SlushLoopProcess :
        /\ pc[lp] = "waitReplies"
        /\ LET s == sample[lp] IN
           /\ \A n2 \in s :
                \E r \in msgs :
                   /\ r.type = "reply"
                   /\ r.dst  = lp
                   /\ r.src  = HostQuery(n2)
        /\ LET replies == { r \in msgs : r.type = "reply" /\ r.dst = lp } IN
           cntRed  == Cardinality({ r \in replies : r.color = "Red" })
           cntBlue == Cardinality({ r \in replies : r.color = "Blue" })
           newCol  == IF cntRed  >= PickFlipThreshold THEN "Red"
                     ELSE IF cntBlue >= PickFlipThreshold THEN "Blue"
                     ELSE color[HostNode(lp)]
        /\ color' = [color EXCEPT ![HostNode(lp)] = newCol]
        /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
        /\ pc' = [pc EXCEPT ![lp] =
                 IF iter'[lp] = SlushIterationCount
                 THEN "done"
                 ELSE "sample"]
        /\ msgs' = msgs \cup
            IF iter'[lp] = SlushIterationCount
            THEN { [type  |-> "term",
                    src   |-> lp,
                    dst   |-> "All",
                    color |-> NoMessage] }
            ELSE {}
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ UNCHANGED <<>>

(* 6. Query processes terminate when all loop processes have broadcast termination *)
QueryDone ==
  /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "replyLoop"
        /\ Cardinality({ m \in msgs : m.type = "term" }) = Cardinality(SlushLoopProcess)
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, msgs, sample, iter>>

(* ----------------------------------------------------------------- *)
(*   Next-state relation                                              *)
(* ----------------------------------------------------------------- *)

Next ==
  \/ ClientAssign
  \/ LoopRequireColor
  \/ LoopSample
  \/ QueryRespond
  \/ LoopTally
  \/ QueryDone

(* ----------------------------------------------------------------- *)
(*   Specification                                                    *)
(* ----------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------- *)
(*   Type invariant                                                   *)
(* ----------------------------------------------------------------- *)

TypeInvariant ==
  /\ color \in [Node -> (Color \cup {NoColor})]
  /\ msgs \subseteq Message

====