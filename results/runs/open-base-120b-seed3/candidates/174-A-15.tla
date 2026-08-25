---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(*  Constants (to be supplied by the .cfg file)                           *)
(*  -------------------------------------------------------------------   *)
(*  Node                : the set of node identifiers                     *)
(*  SlushLoopProcess    : the set of loop processes (one per node)        *)
(*  SlushQueryProcess   : the set of query processes (one per node)       *)
(*  HostMapping         : a set of triples <<loop,query,node>> linking    *)
(*                        each loop and query process to its host node    *)
(*  SlushIterationCount : maximum number of iterations each loop may run *)
(*  SampleSetSize       : size of the peer sample taken each round        *)
(*  PickFlipThreshold   : number of equal replies needed to flip color    *)
(*  NoColor             : special value meaning “uncolored”               *)
(*  NoMessage           : special value meaning “no message”              *)
(***************************************************************************)

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

(***************************************************************************)
(*  Derived sets and types                                                *)
(***************************************************************************)

\* The two possible colors (the protocol’s opinion space)
Colors == {"Red", "Blue"}

\* All admissible messages in the system
Message == [type   : {"query", "reply", "term"},
            src    : (SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage}),
            dst    : (SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage}),
            color  : (Colors \cup {NoColor})]

\* Helper predicates for extracting the host node of a process
LoopHost(p) == 
    CHOOSE n \in Node : <<p, _, n>> \in HostMapping

QueryHost(q) == 
    CHOOSE n \in Node : <<_, q, n>> \in HostMapping

(***************************************************************************)
(*  Variables                                                            *)
(***************************************************************************)

VARIABLES
    colors,   \* [Node -> (Colors \cup {NoColor})]  current color of each node
    msgs,     \* set of in‑flight Message records
    iter,     \* [SlushLoopProcess -> Nat] number of completed iterations per loop
    sample    \* [SlushLoopProcess -> SUBSET Node] current sampled peers

vars == <<colors, msgs, iter, sample>>

(***************************************************************************)
(*  Initialization                                                        *)
(***************************************************************************)

Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ sample = [p \in SlushLoopProcess |-> {}]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Client assigns a random color to an uncolored node
AssignColor ==
    \E n \in Node :
        /\ colors[n] = NoColor
        /\ \/ colors' = [colors EXCEPT ![n] = "Red"]
           \/ colors' = [colors EXCEPT ![n] = "Blue"]
        /\ UNCHANGED <<msgs, iter, sample>>

\* Loop process p selects a fresh sample of distinct peers (excluding itself)
SelectSample(p) ==
    /\ p \in SlushLoopProcess
    /\ colors[LoopHost(p)] # NoColor                \* node already colored
    /\ sample[p] = {}                               \* not already sampling
    /\ LET peers == Node \ {LoopHost(p)} IN
          sample' = [sample EXCEPT ![p] = 
                     CHOOSE s \subseteq peers :
                       Cardinality(s) = SampleSetSize]
    /\ UNCHANGED <<colors, msgs, iter>>

\* Loop process p sends a query message to each sampled peer q
SendQueries(p) ==
    /\ p \in SlushLoopProcess
    /\ sample[p] # {}                               \* a sample exists
    /\ \A n \in sample[p] :
          \E q \in SlushQueryProcess :
                QueryHost(q) = n
    /\ msgs' = msgs \cup
               { [type  |-> "query",
                  src   |-> p,
                  dst   |-> q,
                  color |-> colors[LoopHost(p)] ] :
                 q \in SlushQueryProcess /\ QueryHost(q) \in sample[p] }
    /\ UNCHANGED <<colors, iter, sample>>

\* Query process q receives a query, possibly adopts the queried color,
\* and replies with its (new) color
RespondQuery ==
    \E m \in msgs :
        /\ m.type = "query"
        /\ q = m.dst
        /\ q \in SlushQueryProcess
        /\ n = QueryHost(q)                          \* node hosted by q
        /\ LET newColor == 
                IF colors[n] = NoColor 
                THEN m.color 
                ELSE colors[n] 
           IN
           /\ colors' = [colors EXCEPT ![n] = newColor]
        /\ msgs' = (msgs \ {m}) \cup
                   { [type  |-> "reply",
                      src   |-> q,
                      dst   |-> m.src,
                      color |-> newColor] }
        /\ UNCHANGED <<iter, sample>>

\* Loop process p tallies replies for its current sample;
\* if a color reaches the flip threshold it adopts that color.
TallyAndFlip(p) ==
    /\ p \in SlushLoopProcess
    /\ sample[p] # {}                               \* a sample exists
    /\ \A r \in msgs :
          (r.type = "reply" /\ r.dst = p) => TRUE   \* all replies are present
    /\ LET replies == 
            { r.color : r \in msgs /\ r.type = "reply" /\ r.dst = p } 
        IN
        /\ \E c \in Colors :
               Cardinality({ r \in msgs : 
                               r.type = "reply" /\ r.dst = p /\ r.color = c }) 
               >= PickFlipThreshold
        /\ colors' = [colors EXCEPT ![LoopHost(p)] = 
                        CHOOSE c \in Colors :
                            Cardinality({ r \in msgs : 
                                           r.type = "reply" /\ r.dst = p /\ r.color = c }) 
                            >= PickFlipThreshold ]
    /\ msgs'   = msgs \ { r \in msgs : r.type = "reply" /\ r.dst = p }
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iter'   = [iter EXCEPT ![p] = @ + 1]
    /\ UNCHANGED << >>

\* After completing the prescribed number of iterations, a loop process
\* broadcasts a termination message to all query processes.
SendTermination(p) ==
    /\ p \in SlushLoopProcess
    /\ iter[p] = SlushIterationCount
    /\ msgs' = msgs \cup
               { [type |-> "term",
                  src  |-> p,
                  dst  |-> q,
                  color|-> NoColor] :
                 q \in SlushQueryProcess }
    /\ UNCHANGED <<colors, iter, sample>>

\* Query processes exit (become inert) when they have received termination
\* messages from every loop process.
QueryExit ==
    \E q \in SlushQueryProcess :
        /\ \A p \in SlushLoopProcess :
               \E m \in msgs :
                  /\ m.type = "term"
                  /\ m.src  = p
                  /\ m.dst  = q
        /\ msgs' = msgs \ { m \in msgs : m.type = "term" /\ m.dst = q }
        /\ UNCHANGED <<colors, iter, sample>>

\* The overall Next relation is the disjunction of all possible actions.
Next ==
    \/ AssignColor
    \/ \E p \in SlushLoopProcess : SelectSample(p)
    \/ \E p \in SlushLoopProcess : SendQueries(p)
    \/ RespondQuery
    \/ \E p \in SlushLoopProcess : TallyAndFlip(p)
    \/ \E p \in SlushLoopProcess : SendTermination(p)
    \/ QueryExit

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant (safety)                                               *)
(***************************************************************************)

TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]

=============================================================================