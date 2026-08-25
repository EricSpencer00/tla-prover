---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                     \* set of all node identifiers
    SlushLoopProcess,         \* one loop process per node
    SlushQueryProcess,        \* one query process per node
    HostMapping,              \* set of triples <<node, queryProc, loopProc>>
    SlushIterationCount,      \* number of iterations each loop process performs
    SampleSetSize,            \* size of the peer sample taken each round
    PickFlipThreshold,        \* minimum number of equal-colored replies to flip
    NoColor,                  \* sentinel for an uncolored node
    NoMessage                 \* sentinel for the absence of a message

\* --------------------------------------------------------------------------
\* The two possible colors.  They are not required to be constants in the
\* configuration, but they are useful for the type invariant.
\* --------------------------------------------------------------------------
CONSTANTS Red, Blue
ASSUME ColorSet == {"Red","Blue"}

\* --------------------------------------------------------------------------
\* Message record definition (used only in the type invariant).
\* --------------------------------------------------------------------------
Message ==
  [ type  : {"query","reply","term"},
    src   : (SlushLoopProcess \cup SlushQueryProcess),
    dst   : (SlushLoopProcess \cup SlushQueryProcess),
    color : (Red \cup Blue) \cup {NoColor} ]

\* --------------------------------------------------------------------------
\* PlusCal algorithm describing Slush.
\* --------------------------------------------------------------------------
(*--algorithm SlushAlg
variables
    col    = [n \in Node |-> NoColor],
    msgs   = {},
    sample = [p \in SlushLoopProcess |-> {}],
    iter   = [p \in SlushLoopProcess |-> 0];

begin
  client:
    while \E n \in Node : col[n] = NoColor do
      with n \in Node \ { n \in Node : col[n] # NoColor } do
        with c \in {"Red","Blue"} do
          col := [col EXCEPT ![n] = c];
        end with;
      end with;
    end while;

  loop(p \in SlushLoopProcess):
    await \E n \in Node :
          (\E q \in SlushQueryProcess : <<n,q,p>> \in HostMapping) /\ col[n] # NoColor;
    while iter[p] < SlushIterationCount do
      \* ---- pick a sample of peers (n is the node hosted by p) ----
      with n = CHOOSE n \in Node : <<n,q,p>> \in HostMapping do
        with s \in SUBSET Node :
              Cardinality(s) = SampleSetSize /\ n \notin s do
          sample := [sample EXCEPT ![p] = s];
          \* ---- send a query to each sampled node's query process ----
          with rs = { [type  |-> "query",
                      src   |-> p,
                      dst   |-> q,
                      color |-> col[n]] :
                      q \in { q' \in SlushQueryProcess :
                              <<node,q',lp>> \in HostMapping /\
                              node \in s } } do
            msgs := msgs \cup rs;
          end with;
        end with;
      end with;

      \* ---- wait for all replies ----
      await \A q \in sample[p] :
            \E m \in msgs :
                m.type = "reply" /\ m.dst = p /\ m.src = q;

      \* ---- tally the replies ----
      let reds  == Cardinality({ m \in msgs :
                                   m.type = "reply" /\ m.dst = p /\ m.color = "Red"});
          blues == Cardinality({ m \in msgs :
                                   m.type = "reply" /\ m.dst = p /\ m.color = "Blue"})
      in
        if reds >= PickFlipThreshold then
          col := [col EXCEPT ![n] = "Red"]
        elsif blues >= PickFlipThreshold then
          col := [col EXCEPT ![n] = "Blue"]
        else
          Skip
        end if;

      \* ---- clean up for the next round ----
      msgs   := msgs \ { m \in msgs : m.dst = p };
      sample := [sample EXCEPT ![p] = {}];
      iter   := [iter EXCEPT ![p] = @ + 1];
    end while;

    \* ---- broadcast termination to all query processes ----
    msgs := msgs \cup { [type  |-> "term",
                         src   |-> p,
                         dst   |-> q,
                         color |-> NoColor] :
                         q \in SlushQueryProcess };
  end process;

  query(q \in SlushQueryProcess):
    while TRUE do
      await \E m \in msgs :
            m.type = "query" /\ m.dst = q;
      with m \in msgs :
            m.type = "query" /\ m.dst = q do
        with n = CHOOSE n \in Node : <<n,q,lp>> \in HostMapping do
          if col[n] = NoColor then
            col := [col EXCEPT ![n] = m.color];
          end if;
          msgs := msgs \cup { [type  |-> "reply",
                               src   |-> q,
                               dst   |-> m.src,
                               color |-> col[n]] };
        end with;
      end with;
    end while;
  end process;
end algorithm;*)

\* --------------------------------------------------------------------------
\* The PlusCal translator creates the following identifiers:
\*   col, msgs, sample, iter   – the state variables
\*   Init, Next, vars          – the standard TLA+ definitions
\* --------------------------------------------------------------------------

\* The specification (required identifier)
Spec == Init /\ [] [Next]_vars

\* Type invariant (required identifier)
TypeInvariant ==
  /\ col \in [Node -> (Red \cup Blue \cup {NoColor})]
  /\ msgs \subseteq Message
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iter \in [SlushLoopProcess -> Nat]

====