---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                  \* the set of node identifiers
    SlushLoopProcess,      \* one loop process per node
    SlushQueryProcess,     \* one query process per node
    HostMapping,           \* set of triples <<n, lp, qp>> linking a node n to its loop lp and query qp
    SlushIterationCount,   \* number of iterations each loop process should perform
    SampleSetSize,         \* size of the peer sample each iteration
    PickFlipThreshold,     \* number of equal replies required to flip a node's color
    NoColor,               \* sentinel for an uncolored node
    NoMessage              \* sentinel for “no message”

(***************************************************************************)
(*  Colors                                                                *)
(***************************************************************************)

Color == {"Red", "Blue"}

(***************************************************************************)
(*  Helper functions to extract the host node of a loop or query process   *)
(***************************************************************************)

HostLoop(lp) == 
    CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

HostQuery(qp) ==
    CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

Host(p) == 
    IF p \in SlushLoopProcess THEN HostLoop(p) ELSE HostQuery(p)

(***************************************************************************)
(*  Inverse mapping from a query process to its host node                  *)
(***************************************************************************)

HostOfQuery(qp) == HostQuery(qp)

(***************************************************************************)
(*  Message datatype                                                      *)
(***************************************************************************)

Message ==
    [type   : {"Query", "Reply", "Term"},
     from   : SlushLoopProcess \cup SlushQueryProcess,
     to     : SlushLoopProcess \cup SlushQueryProcess \cup {"All"},
     color  : Color \cup {NoColor}]

(***************************************************************************)
(*  Nondeterministic choice helpers                                        *)
(***************************************************************************)

RandomColor == CHOOSE c \in Color : TRUE

RandomSubset(S, k) ==
    CHOOSE sub \in SUBSET S : Cardinality(sub) = k

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)

VARIABLES
    color,      \* [node \in Node |-> Color \cup {NoColor}]
    msgs,       \* set of messages currently in flight
    sample,     \* [lp \in SlushLoopProcess |-> SUBSET Node]  -- current peer sample
    iter,       \* [lp \in SlushLoopProcess |-> Nat]         -- iterations done
    pc          \* program counters for all processes

vars == <<color, msgs, sample, iter, pc>>

(***************************************************************************)
(*  Initialization                                                         *)
(***************************************************************************)

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc = [proc \in {"Client"} \cup SlushLoopProcess \cup SlushQueryProcess |-> 
            IF proc = "Client" THEN "Assign"
            ELSIF proc \in SlushLoopProcess THEN "WaitColor"
            ELSE "ReplyLoop"]

(***************************************************************************)
(*  Actions                                                                *)
(***************************************************************************)

(*************************)
(*  1. Client assigns a color to an uncolored node               *)
(*************************)
ClientAssign ==
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ LET c == RandomColor IN
                color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, sample, iter, pc>>
    /\ pc' = [pc EXCEPT !["Client"] = "Assign"]

(*************************)
(*  2. Loop process waits until its node is colored              *)
(*************************)
LoopWaitColor ==
    /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "WaitColor"
          /\ color[HostLoop(lp)] # NoColor
          /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(*************************)
(*  3. Loop process selects a sample and sends queries           *)
(*************************)
LoopSample ==
    /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "Sample"
          /\ LET peers == RandomSubset(Node \ {HostLoop(lp)}, SampleSetSize) IN
                /\ sample' = [sample EXCEPT ![lp] = peers]
                /\ msgs'   = msgs \cup
                             { [type  |-> "Query",
                                from  |-> lp,
                                to    |-> qp,
                                color |-> color[HostLoop(lp)] ] :
                               qp \in { HostQuery(q) : q \in peers } }
                /\ pc' = [pc EXCEPT ![lp] = "WaitReplies"]
    /\ UNCHANGED <<color, iter>>

(*************************)
(*  4. Loop process tallies replies and possibly flips its color *)
(*************************)
LoopTallyAndUpdate ==
    /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "WaitReplies"
          /\ \A qp \in sample[lp] :
                \E m \in msgs :
                    /\ m.type = "Reply"
                    /\ m.from = HostQuery(qp)
                    /\ m.to   = lp
          /\ LET
                reds  == Cardinality({ m \in msgs : m.type = "Reply" /\ m.to = lp /\ m.color = "Red" })
                blues == Cardinality({ m \in msgs : m.type = "Reply" /\ m.to = lp /\ m.color = "Blue" })
                newColor ==
                    IF reds >= PickFlipThreshold THEN "Red"
                    ELSE IF blues >= PickFlipThreshold THEN "Blue"
                    ELSE color[HostLoop(lp)]
            IN
                /\ color' = [color EXCEPT ![HostLoop(lp)] = newColor]
                /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
                /\ sample' = [sample EXCEPT ![lp] = {}]
                /\ pc' = [pc EXCEPT ![lp] =
                         IF iter'[lp] < SlushIterationCount THEN "Sample"
                         ELSE "Terminate"]
    /\ UNCHANGED msgs

(*************************)
(*  5. Loop process broadcasts termination message                *)
(*************************)
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
          /\ pc[lp] = "Terminate"
          /\ msgs' = msgs \cup { [type |-> "Term", from |-> lp, to |-> "All", color |-> NoColor] }
          /\ pc'   = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

(*************************)
(*  6. Query process handles a query and replies                  *)
(*************************)
QueryHandle ==
    /\ \E qp \in SlushQueryProcess :
          /\ pc[qp] = "ReplyLoop"
          /\ \E m \in msgs :
                /\ m.type = "Query"
                /\ m.to   = qp
                /\ LET n == HostOfQuery(qp) IN
                      /\ color' = 
                         IF color[n] = NoColor
                         THEN [color EXCEPT ![n] = m.color]
                         ELSE color
                      /\ msgs' = (msgs \ {m}) \cup
                                 { [type  |-> "Reply",
                                    from  |-> qp,
                                    to    |-> m.from,
                                    color |-> color'[n] ] }
          /\ pc' = [pc EXCEPT ![qp] = "ReplyLoop"]
    /\ UNCHANGED <<sample, iter>>

(*************************)
(*  7. Query process exits when all loop processes have terminated*)
(*************************)
QueryExit ==
    /\ \E qp \in SlushQueryProcess :
          /\ pc[qp] = "ReplyLoop"
          /\ \A lp \in SlushLoopProcess :
                \E t \in msgs :
                    /\ t.type = "Term"
                    /\ t.from = lp
          /\ pc' = [pc EXCEPT ![qp] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
    \/ ClientAssign
    \/ LoopWaitColor
    \/ LoopSample
    \/ LoopTallyAndUpdate
    \/ LoopTerminate
    \/ QueryHandle
    \/ QueryExit

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)

Spec == Init /\ [] [Next]_vars

(***************************************************************************)
(*  Type invariant                                                         *)
(***************************************************************************)

TypeInvariant ==
    /\ color \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message

====