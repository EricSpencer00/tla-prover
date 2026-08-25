---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*---------------------------------------------------------------------*)
(* Constants required by the .cfg file                                  *)
(*---------------------------------------------------------------------*)
CONSTANTS
    Node,                     \* Set of node identifiers
    SlushLoopProcess,         \* Set of loop process identifiers
    SlushQueryProcess,        \* Set of query process identifiers
    HostMapping,              \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,      \* Number of iterations each loop process executes
    SampleSetSize,            \* Size of the random peer sample
    PickFlipThreshold,        \* Threshold for flipping color
    NoColor,                  \* Distinguished value meaning "uncolored"
    NoMessage                 \* Distinguished value meaning "no message"

(*---------------------------------------------------------------------*)
(* Derived sets and definitions                                         *)
(*---------------------------------------------------------------------*)
CONSTANT Colors == {"Red", "Blue"}

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            col  : (Colors \cup {NoColor})]

Process == {"client"} \cup SlushLoopProcess \cup SlushQueryProcess

(* Helper functions to navigate HostMapping *)
LoopOfNode(n)    == CHOOSE t \in HostMapping : t[1] = n
QueryOfNode(n)   == CHOOSE t \in HostMapping : t[1] = n

NodeOfLoop(l)    == CHOOSE t \in HostMapping : t[2] = l
NodeOfQuery(q)   == CHOOSE t \in HostMapping : t[3] = q

(*---------------------------------------------------------------------*)
(* Variables                                                            *)
(*---------------------------------------------------------------------*)
VARIABLES
    color,      \* [Node -> (Colors \cup {NoColor})]
    msgs,       \* Subset of Message
    sample,     \* [SlushLoopProcess -> SUBSET Node]   (current peer sample)
    iter,       \* [SlushLoopProcess -> Nat]           (iterations done)
    pc,         \* [Process -> Str]                    (program counters)
    termCount   \* Nat                                   (number of termination msgs received)

(*---------------------------------------------------------------------*)
(* Initial state                                                        *)
(*---------------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ pc = [p \in Process |-> 
                IF p = "client"          THEN "AssignColor"
                ELSE IF p \in SlushLoopProcess THEN "WaitColor"
                ELSE "ReplyLoop"]
    /\ termCount = 0

(*---------------------------------------------------------------------*)
(* Actions                                                              *)
(*---------------------------------------------------------------------*)

(* 1. Client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ pc["client"] = "AssignColor"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Colors :
          /\ color' = [color EXCEPT ![n] = c]
          /\ UNCHANGED <<msgs, sample, iter, pc, termCount>>
          /\ pc' = [pc EXCEPT !["client"] = "AssignColor"]
    /\ UNCHANGED <<color, msgs, sample, iter, pc, termCount>> 
    \/ (* No uncolored nodes left: client becomes idle *)
      /\ pc["client"] = "AssignColor"
      /\ \A n \in Node : color[n] # NoColor
      /\ UNCHANGED <<color, msgs, sample, iter, pc, termCount>>
      /\ pc' = [pc EXCEPT !["client"] = "Done"]

(* 2. Loop process waits until its host node is colored *)
LoopWaitColor(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "WaitColor"
    /\ color[NodeOfLoop(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter, termCount>>

(* 3. Loop process selects a sample and sends query messages *)
LoopSample(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Sample"
    /\ iter[p] < SlushIterationCount
    /\ LET otherNodes == Node \ {NodeOfLoop(p)} IN
       \E s \in SUBSET otherNodes :
           /\ Cardinality(s) = SampleSetSize
           /\ sample' = [sample EXCEPT ![p] = s]
           /\ msgs' = msgs \cup {
                   [type |-> "query",
                    src  |-> p,
                    dst  |-> QueryOfNode(q),
                    col  |-> color[NodeOfLoop(p)]]
                 : q \in s}
           /\ pc' = [pc EXCEPT ![p] = "AwaitReplies"]
           /\ UNCHANGED <<color, iter, termCount>>

(* 4. Query process receives a query, possibly adopts color, replies *)
QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "ReplyLoop"
    /\ \E m \in msgs :
         /\ m.type = "query"
         /\ m.dst  = q
         /\ LET n == NodeOfQuery(q) IN
            /\ IF color[n] = NoColor
               THEN color' = [color EXCEPT ![n] = m.col]
               ELSE UNCHANGED color
            /\ msgs'' = msgs \cup {
                   [type |-> "reply",
                    src  |-> q,
                    dst  |-> m.src,
                    col  |-> IF color[n] = NoColor THEN m.col ELSE color[n]]
               }
            /\ msgs' = msgs \ {m}
            /\ UNCHANGED <<sample, iter, pc, termCount>>
    /\ pc' = [pc EXCEPT ![q] = "ReplyLoop"]  \* stays in loop

(* 5. Loop process tallies replies and possibly flips color *)
LoopTally(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "AwaitReplies"
    /\ \A q \in sample[p] :
         \E r \in msgs :
            /\ r.type = "reply"
            /\ r.dst  = p
            /\ r.src  = QueryOfNode(q)
    /\ LET reds   == Cardinality({ q \in sample[p] :
                                   \E r \in msgs :
                                      /\ r.type = "reply"
                                      /\ r.dst = p
                                      /\ r.src = QueryOfNode(q)
                                      /\ r.col = "Red"})
          blues  == Cardinality({ q \in sample[p] :
                                   \E r \in msgs :
                                      /\ r.type = "reply"
                                      /\ r.dst = p
                                      /\ r.src = QueryOfNode(q)
                                      /\ r.col = "Blue"})
          newCol == IF reds >= PickFlipThreshold THEN "Red"
                    ELSE IF blues >= PickFlipThreshold THEN "Blue"
                    ELSE color[NodeOfLoop(p)]
    IN
      /\ color' = [color EXCEPT ![NodeOfLoop(p)] = newCol]
      /\ sample' = [sample EXCEPT ![p] = {}]
      /\ iter'   = [iter EXCEPT ![p] = @ + 1]
      /\ pc' = [pc EXCEPT ![p] = 
                IF iter'[p] = SlushIterationCount THEN "Terminate"
                ELSE "Sample"]
      /\ UNCHANGED msgs
      /\ UNCHANGED termCount

(* 6. Loop process broadcasts termination message *)
LoopTerminate(p) ==
    /\ p \in SlushLoopProcess
    /\ pc[p] = "Terminate"
    /\ msgs' = msgs \cup {
                [type |-> "term",
                 src  |-> p,
                 dst  |-> "client",
                 col  |-> NoColor]}
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<color, sample, iter, termCount>>

(* 7. Query processes exit when all loop processes have terminated *)
QueryExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "ReplyLoop"
    /\ termCount = Cardinality(SlushLoopProcess)
    /\ pc' = [pc EXCEPT ![q] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter, termCount>>

(* 8. Client receives termination messages and counts them *)
ClientReceiveTerm ==
    /\ pc["client"] = "Done"
    /\ \E m \in msgs :
         /\ m.type = "term"
         /\ m.dst = "client"
    /\ msgs' = msgs \ {m}
    /\ termCount' = termCount + 1
    /\ UNCHANGED <<color, sample, iter, pc>>

(*---------------------------------------------------------------------*)
(* Next-state relation                                                   *)
(*---------------------------------------------------------------------*)
Next ==
    \/ \E p \in SlushLoopProcess : LoopWaitColor(p)
    \/ \E p \in SlushLoopProcess : LoopSample(p)
    \/ \E p \in SlushLoopProcess : LoopTally(p)
    \/ \E p \in SlushLoopProcess : LoopTerminate(p)
    \/ ClientAssign
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientReceiveTerm

(*---------------------------------------------------------------------*)
(* Specification                                                         *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc, termCount>>

(*---------------------------------------------------------------------*)
(* Type invariant                                                       *)
(*---------------------------------------------------------------------*)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [Process -> Str]
    /\ termCount \in Nat

====