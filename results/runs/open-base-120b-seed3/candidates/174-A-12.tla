---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop process performs
    SampleSetSize,       \* Size of the peer sample taken each iteration
    PickFlipThreshold,   \* Threshold for flipping to a color
    NoColor,             \* Value representing an uncolored node
    NoMessage             \* Placeholder for “no message”

(***************************************************************************)
\*--- CONSTANT DEFINITIONS -------------------------------------------------
\* Colors used in the protocol (two actual colors plus the uncolored value)
Colors == {"Red", "Blue", NoColor}

\* Helper functions that extract the node associated with a loop or query process
NodeOfLoop(lp) == 
    CHOOSE n \in Node : 
        \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

NodeOfQuery(qp) ==
    CHOOSE n \in Node :
        \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

LoopOfNode(n) ==
    CHOOSE lp \in SlushLoopProcess :
        \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping

QueryOfNode(n) ==
    CHOOSE qp \in SlushQueryProcess :
        \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

\*--- MESSAGE DEFINITION --------------------------------------------------
Message == 
    [type   : {"query","reply","term"},
     from   : (SlushLoopProcess \cup SlushQueryProcess),
     to     : (SlushLoopProcess \cup SlushQueryProcess),
     color  : {"Red","Blue", NoColor}]   \* “color” is ignored for “term” messages

\*--- STATE VARIABLES ------------------------------------------------------
VARIABLES
    color,   \* [node \in Node |-> Colors]   current color of each node
    msgs,    \* Set of messages currently in‑flight
    sample,  \* [lp \in SlushLoopProcess |-> SUBSET Node]   peers sampled this round
    iter,    \* [lp \in SlushLoopProcess |-> Nat]   number of completed iterations
    pc       \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> Nat]   program counters (used by PlusCal)

\*--- INITIAL STATE --------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]
    /\ pc     = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0]

\*--- THE ALGORITHM (PLUSCAL) -----------------------------------------------
\* The algorithm is written in PlusCal; the TLA+ translation will generate the
\* Init and Next actions automatically.
\* The PlusCal code follows the description in the problem statement.

\* BEGIN PLUSCAL
--algorithm SlushAlg {
variables
    color = [n \in Node |-> NoColor],
    msgs   = {},
    sample = [lp \in SlushLoopProcess |-> {}],
    iter   = [lp \in SlushLoopProcess |-> 0],
    pc     = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0];

process (Client = "Client")
{
  label "ClientLoop";
  while (TRUE) {
    if (\E n \in Node : color[n] = NoColor) {
      with n \in { n \in Node : color[n] = NoColor } do
        either
          color' := [color EXCEPT ![n] = "Red"];
        or
          color' := [color EXCEPT ![n] = "Blue"];
        end either;
      end with;
    } else {
      skip;               \* all nodes colored – client can stop
      break "ClientLoop";
    };
  }
}

process (Loop = SlushLoopProcess)
{
  variable node  \* the node this loop process drives;
  node := NodeOfLoop(self);

  label "WaitColor";
  while (color[node] = NoColor) {
    skip;                 \* spin until the node receives an initial color
  }

  label "Iterate";
  while (iter[self] < SlushIterationCount) {
    \* ---- sample peers ----------------------------------------------------
    sample' := [sample EXCEPT ![self] = 
                 CHOOSE S \subseteq (Node \ {node}) :
                   Cardinality(S) = SampleSetSize];

    \* ---- send queries ----------------------------------------------------
    with peer \in sample'[self] do
      let qp == QueryOfNode(peer) in
        msgs' := msgs \cup {
          [type |-> "query",
           from |-> self,
           to   |-> qp,
           color|-> color[node]]
        };
    end with;

    \* ---- collect replies -------------------------------------------------
    variable replies = {};
    while (Cardinality(replies) < SampleSetSize) {
      with m \in msgs do
        if (m.type = "reply" /\ m.to = self) {
          msgs' := msgs \ {m};
          replies := replies \cup {m.color};
        } else {
          skip;
        };
      end with;
    }

    \* ---- tally and possibly flip -----------------------------------------
    let redCount  == Cardinality({c \in replies : c = "Red"});
        blueCount == Cardinality({c \in replies : c = "Blue"});
    in
      if (redCount >= PickFlipThreshold) {
        color' := [color EXCEPT ![node] = "Red"];
      } elsif (blueCount >= PickFlipThreshold) {
        color' := [color EXCEPT ![node] = "Blue"];
      } else {
        skip;
      };

    \* ---- cleanup ---------------------------------------------------------
    sample' := [sample EXCEPT ![self] = {}];
    iter'   := [iter   EXCEPT ![self] = @ + 1];
  }

  \* ---- broadcast termination -------------------------------------------
  with qp \in SlushQueryProcess do
    msgs' := msgs \cup {
      [type |-> "term",
       from |-> self,
       to   |-> qp,
       color|-> NoColor]
    };
  end with;

  skip;               \* loop process terminates (no further actions)
}

process (Query = SlushQueryProcess)
{
  variable node;
  node := NodeOfQuery(self);

  label "QueryLoop";
  while (TRUE) {
    with m \in msgs do
      if (m.type = "query" /\ m.to = self) {
        msgs' := msgs \ {m};

        \* adopt the queried color if still uncolored
        if (color[node] = NoColor) {
          color' := [color EXCEPT ![node] = m.color];
        } else {
          skip;
        };

        \* reply back to the querying loop process
        msgs' := msgs' \cup {
          [type |-> "reply",
           from |-> self,
           to   |-> m.from,
           color|-> color[node]]
        };
      } elsif (m.type = "term" /\ m.to = self) {
        msgs' := msgs \ {m};
        break "QueryLoop";   \* exit when termination message received
      } else {
        skip;
      };
    end with;
  }
}
}
\* END PLUSCAL

\*--- NEXT ACTION -----------------------------------------------------------
Next ==
    \/ Client
    \/ Loop
    \/ Query

\*--- SPECIFICATION ---------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

\*--- TYPE INVARIANT --------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> Nat]

=============================================================================