---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Node,                \* Set of node identifiers
  SlushLoopProcess,    \* Set of loop process identifiers
  SlushQueryProcess,   \* Set of query process identifiers
  HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
  SlushIterationCount, \* Number of iterations each loop process performs
  SampleSetSize,       \* Size of the peer sample taken each round
  PickFlipThreshold,   \* Minimum number of equal replies needed to flip
  NoColor,             \* Symbol for the uncolored state
  NoMessage             \* Symbol for the absence of a message

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Color == {"Red", "Blue", NoColor}

MessageType == {"query", "reply", "term"}

Message == [type   : MessageType,
            src    : Proc,
            dst    : Proc,
            color  : Color]

Proc == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

\* Randomly choose a subset of size k from a set s (non‑deterministic)
RandomSample(s, k) == 
  CHOOSE sub \in SUBSET s : Cardinality(sub) = k

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(*--algorithm Slush
variables
  color  = [n \in Node |-> NoColor],
  msgs   = {},
  sample = [p \in SlushLoopProcess |-> {}],
  iter   = [p \in SlushLoopProcess |-> 0];

process (client) {
  while TRUE do
    if \E n \in Node : color[n] = NoColor then
      with n \in Node do
        if color[n] = NoColor then
          either
            color' := [color EXCEPT ![n] = "Red"];
          or
            color' := [color EXCEPT ![n] = "Blue"];
          end either;
        end if;
      end with;
    else
      goto Done;
    end if;
  end while;
Done:
  skip;
}

process (lp \in SlushLoopProcess) {
  variable myNode;
  myNode := CHOOSE n \in Node : <<n, lp, _>> \in HostMapping;
  while color[myNode] = NoColor do
    await TRUE; \* wait until the node is colored
  end while;

  while iter[lp] < SlushIterationCount do
    \* ---- sample peers -------------------------------------------------
    sample' := [sample EXCEPT ![lp] = RandomSample(Node \ {myNode}, SampleSetSize)];
    \* ---- send queries -------------------------------------------------
    with q \in sample'[lp] do
      let qp == CHOOSE qp \in SlushQueryProcess : <<q, _, qp>> \in HostMapping in
        msgs' := msgs \cup {[type |-> "query",
                            src  |-> lp,
                            dst  |-> qp,
                            color|-> color[myNode]]};
      end let;
    end with;

    \* ---- wait for all replies ----------------------------------------
    await \A q \in sample[lp] :
            \E m \in msgs :
               /\ m.type = "reply"
               /\ m.dst  = lp
               /\ m.src  = CHOOSE qp \in SlushQueryProcess : <<q, _, qp>> \in HostMapping;

    \* ---- tally replies -----------------------------------------------
    let reds  == Cardinality({m \in msgs : m.type = "reply" /\ m.dst = lp /\ m.color = "Red"});
        blues == Cardinality({m \in msgs : m.type = "reply" /\ m.dst = lp /\ m.color = "Blue"}) in
      if reds >= PickFlipThreshold then
        color' := [color EXCEPT ![myNode] = "Red"];
      elsif blues >= PickFlipThreshold then
        color' := [color EXCEPT ![myNode] = "Blue"];
      else
        skip;
      end if;
    end let;

    \* ---- clean up and advance -----------------------------------------
    sample' := [sample EXCEPT ![lp] = {}];
    iter'   := [iter EXCEPT ![lp] = @ + 1];
  end while;

  \* ---- broadcast termination -----------------------------------------
  with qp \in SlushQueryProcess do
    msgs' := msgs \cup {[type |-> "term",
                        src  |-> lp,
                        dst  |-> qp,
                        color|-> NoColor]};
  end with;
  goto Done;
Done:
  skip;
}

process (qp \in SlushQueryProcess) {
  variable myNode;
  myNode := CHOOSE n \in Node : <<n, _, qp>> \in HostMapping;
  while TRUE do
    either
      \* ---- handle query -----------------------------------------------
      await \E m \in msgs : m.type = "query" /\ m.dst = qp;
      with m \in msgs : m.type = "query" /\ m.dst = qp do
        if color[myNode] = NoColor then
          color' := [color EXCEPT ![myNode] = m.color];
        end if;
        msgs' := msgs \cup {[type |-> "reply",
                            src  |-> qp,
                            dst  |-> m.src,
                            color|-> color[myNode]]};
        msgs' := msgs \\ {m}; \* remove the processed query
      end with;
    or
      \* ---- handle termination -----------------------------------------
      await \E t \in msgs : t.type = "term" /\ t.dst = qp;
      with t \in msgs : t.type = "term" /\ t.dst = qp do
        msgs' := msgs \\ {t};
        goto Done;
      end with;
    end either;
  end while;
Done:
  skip;
}
end algorithm *)

\* ----------------------------------------------------------------------
\* TLA+ level definitions
\* ----------------------------------------------------------------------
VARIABLES color, msgs, sample, iter

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs   = {}
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter   = [p \in SlushLoopProcess |-> 0]

Next ==
  \/ \E self \in Proc : 
        /\ pc[self] # "Done"
        /\ UNCHANGED <<color, msgs, sample, iter>>

Spec == Init /\ [][Next]_<<color, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ color \in [Node -> Color]
  /\ msgs \subseteq Message

=============================================================================