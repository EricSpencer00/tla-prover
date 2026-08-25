---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  Constants required by the .cfg file                                   *)
(* ---------------------------------------------------------------------  *)
CONSTANTS 
    Node,                 \* Set of all node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers (one per node)
    SlushQueryProcess,    \* Set of query process identifiers (one per node)
    HostMapping,          \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* Number of iterations each loop process performs
    SampleSetSize,        \* Size of the peer sample each iteration
    PickFlipThreshold,    \* Threshold for adopting a color
    NoColor,              \* Special value meaning "uncolored"
    NoMessage              \* Special value used in termination messages

(***************************************************************************)
(*  Derived sets and helper functions                                      *)
(* ---------------------------------------------------------------------  *)

Colors == {"Red", "Blue"}

\* Mapping from a loop process to its host node
NodeOfLoop(l) == 
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

\* Mapping from a query process to its host node
NodeOfQuery(q) == 
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* The set of query processes that correspond to a given set of nodes
QuerySet(S) == 
    { q \in SlushQueryProcess :
        \E n \in S : \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping }

(***************************************************************************)
(*  State variables                                                        *)
(* ---------------------------------------------------------------------  *)

VARIABLES 
    color,   \* [node -> (Colors \cup {NoColor})]
    msgs,    \* set of messages in flight
    sample,  \* [loopProc -> SUBSET Node]   (current sample set)
    iter     \* [loopProc -> Nat]           (iterations completed)

vars == <<color, msgs, sample, iter>>

(***************************************************************************)
(*  Message definition                                                     *)
(* ---------------------------------------------------------------------  *)

Message == 
    [type   : {"query", "reply", "term"},
     src    : (SlushLoopProcess \cup SlushQueryProcess),
     dst    : (SlushLoopProcess \cup SlushQueryProcess),
     color  : (Colors \cup {NoColor, NoMessage})]

(***************************************************************************)
(*  Initial state                                                          *)
(* ---------------------------------------------------------------------  *)

Init == 
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]

(***************************************************************************)
(*  Actions                                                               *)
(* ---------------------------------------------------------------------  *)

\* ------------------------------------------------------------------- *
\*  Client process: repeatedly assign a random color to an uncolored   *
\*  node until all nodes are colored.                                  *
\* ------------------------------------------------------------------- *
ClientAssign ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in Colors :
              /\ color' = [color EXCEPT ![n] = c]
              /\ UNCHANGED <<msgs, sample, iter>>

\* ------------------------------------------------------------------- *
\*  Loop process actions                                               *
\* ------------------------------------------------------------------- *

\* Wait until its host node has a color
LoopWaitColor(l) ==
    LET n == NodeOfLoop(l) IN
        /\ color[n] = NoColor
        /\ UNCHANGED <<color, msgs, sample, iter>>

\* Choose a random sample set and send query messages
LoopSample(l) ==
    LET n == NodeOfLoop(l) IN
    /\ color[n] # NoColor
    /\ iter[l] < SlushIterationCount
    /\ \E S \in SUBSET (Node \ {n}) :
          /\ Cardinality(S) = SampleSetSize
          /\ sample' = [sample EXCEPT ![l] = S]
          /\ LET qs == QuerySet(S) IN
                msgs' = msgs \cup 
                         { [type  |-> "query",
                            src   |-> l,
                            dst   |-> q,
                            color |-> color[n]] : q \in qs }
    /\ UNCHANGED <<color, iter>>

\* Receive all replies, possibly flip color, clear sample, increment iter
LoopReceiveReplies(l) ==
    LET n  == NodeOfLoop(l) ;
        S  == sample[l] ;
        qs == QuerySet(S) ;
        Replies == { m \in msgs :
                     /\ m.type = "reply"
                     /\ m.dst  = l
                     /\ m.src \in qs } 
    IN
    /\ S # {}                       \* there is a pending sample
    /\ Cardinality(Replies) = Cardinality(qs)   \* all replies received
    /\ LET reds  == Cardinality({ m \in Replies : m.color = "Red" }) ;
           blues == Cardinality({ m \in Replies : m.color = "Blue" })
       IN
          IF reds >= PickFlipThreshold THEN
              color' = [color EXCEPT ![n] = "Red"]
          ELSE IF blues >= PickFlipThreshold THEN
              color' = [color EXCEPT ![n] = "Blue"]
          ELSE
              color' = color
    /\ msgs'   = msgs \ Replies
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ iter'   = [iter EXCEPT ![l] = @ + 1]
    /\ UNCHANGED <<>>

\* After completing all iterations, broadcast termination messages
LoopTerminate(l) ==
    /\ iter[l] = SlushIterationCount
    /\ msgs' = msgs \cup 
                { [type  |-> "term",
                   src   |-> l,
                   dst   |-> q,
                   color |-> NoMessage] : q \in SlushQueryProcess }
    /\ UNCHANGED <<color, sample, iter>>

\* ------------------------------------------------------------------- *
\*  Query process actions                                               *
\* ------------------------------------------------------------------- *

\* Respond to a query: possibly adopt the queried color, then reply
QueryRespond(q) ==
    LET n == NodeOfQuery(q) IN
    \E m \in msgs :
        /\ m.type = "query"
        /\ m.dst  = q
        /\ LET colorAfter ==
               IF color[n] = NoColor THEN [color EXCEPT ![n] = m.color] ELSE color
           IN
           /\ color' = colorAfter
           /\ reply  == [type  |-> "reply",
                         src   |-> q,
                         dst   |-> m.src,
                         color |-> colorAfter[n]]
           /\ msgs' = (msgs \ {m}) \cup {reply}
           /\ UNCHANGED <<sample, iter>>

\* Receive a termination message and stop participating
QueryTerminate(q) ==
    \E t \in msgs :
        /\ t.type = "term"
        /\ t.dst  = q
        /\ msgs' = msgs \ {t}
        /\ UNCHANGED <<color, sample, iter>>

(***************************************************************************)
(*  Next-state relation                                                    *)
(* ---------------------------------------------------------------------  *)

Next ==
    \/ ClientAssign
    \/ \E l \in SlushLoopProcess : LoopWaitColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E l \in SlushLoopProcess : LoopReceiveReplies(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E q \in SlushQueryProcess : QueryTerminate(q)

(***************************************************************************)
(*  Specification                                                          *)
(* ---------------------------------------------------------------------  *)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant                                                         *)
(* ---------------------------------------------------------------------  *)

TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq [type   : {"query","reply","term"},
                      src    : (SlushLoopProcess \cup SlushQueryProcess),
                      dst    : (SlushLoopProcess \cup SlushQueryProcess),
                      color  : (Colors \cup {NoColor, NoMessage})]

=============================================================================