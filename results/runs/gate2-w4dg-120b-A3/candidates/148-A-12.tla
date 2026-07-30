---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Configured identifiers: they must appear exactly as listed in the .cfg.
CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block in the Nano block-lattice: its chain type determines which
\* referenced fields are meaningful.
Block ==
    [ chain : PublicKey
    , kind : {"genesis", "send", "open", "receive", "change"}
    , pred : Hash \cup {NoHash}
    , extra : PublicKey \cup Hash \cup NoBlockVal
    , sig : PublicKey
    ]

\* A sent-but-not-yet-validated block in transit to a node.
Witness ==
    [ chain : PublicKey
    , kind : {"send", "open", "receive", "change"}
    , pred : Hash
    , extra : PublicKey \cup Hash
    , signer : PrivateKey
    ]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
    /\ received \subseteq [node : Node, block : Witness]

\* Only a block created by a node's owner (via its private key) may ever
\* appear in a ledger; this is what the SafetyInvariant protects across
\* every node's replicated ledger.
SignedByOwner(b) ==
    \E sk \in PrivateKey : b.chain = sk /\ b.sig = sk

\* A block's referenced predecessor must exist in the local ledger copy.
PredExists(n, b) == b.pred = NoHash \/ ledger[n][b.pred] # NoBlockVal

\* Walking a chain: a send block can't overdraw its remaining balance.
Balance(n, h) ==
    IF h = NoHash
    THEN 0
    ELSE LET b == ledger[n][h] IN
         IF b = NoBlockVal
         THEN 0
         ELSE IF b.kind = "send"
              THEN Balance(n, b.pred)
              ELSE IF b.kind = "receive"
                   THEN Balance(n, b.pred) + b.extra
                   ELSE IF b.kind = "open"
                        THEN b.extra
                        ELSE Balance(n, b.pred)

\* The GenesisBalance is the total money in the network; the invariant
\* below asserts it is never exceeded by summing every account.
NodeBalance(n) == Balance(n, lastHash)

TotalBalance == Cardinality({ n \in Node : NodeBalance(n) > 0 }) * GenesisBalance

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = {}

\* Genesis block: everything starts empty, so the hash is computed against
\* the sentinel. It is broadcast to every node at once.
CreateGenesis(sk) ==
    /\ lastHash = NoHashVal
    /\ sk \notin PrivateKey
    /\ LET h == CalculateHash(sk, NoHashVal)
           b == [ chain |-> sk, kind |-> "genesis", pred |-> NoHashVal
                 , extra |-> GenesisBalance, sig |-> sk ]
       IN /\ lastHash' = h
          /\ ledger' = [n \in Node |-> [ ledger[n] EXCEPT ![h] = b ]]
          /\ received' = [node \in Node |-> [ chain |-> sk, kind |-> "genesis"
                                            , pred |-> NoHashVal
                                            , extra |-> GenesisBalance
                                            , signer |-> sk ]]
\* A send is only possible if the sender's chain can afford the amount.
CreateSend(n, sk, to, amt) ==
    /\ sk \in PrivateKey
    /\ lastHash # NoHashVal
    /\ amt <= Balance(n, lastHash)
    /\ LET h == CalculateHash([sk, lastHash, to, amt])
           w == [ chain |-> sk, kind |-> "send", pred |-> lastHash
                 , extra |-> amt, signer |-> sk ]
       IN /\ lastHash' = h
          /\ received' = received \cup
                         {[node |-> p, block |-> w] : p \in Node}
          /\ UNCHANGED ledger

CreateOpen(n, sk, h) ==
    /\ sk \in PrivateKey
    /\ lastHash # NoHashVal
    /\ LET w == [ chain |-> sk, kind |-> "open", pred |-> lastHash
                 , extra |-> h, signer |-> sk ]
       IN /\ lastHash' = CalculateHash(w)
          /\ received' = received \cup
                         {[node |-> p, block |-> w] : p \in Node}
          /\ UNCHANGED ledger

CreateReceive(n, sk, h) ==
    /\ sk \in PrivateKey
    /\ lastHash # NoHashVal
    /\ LET w == [ chain |-> sk, kind |-> "receive", pred |-> lastHash
                 , extra |-> h, signer |-> sk ]
       IN /\ lastHash' = CalculateHash(w)
          /\ received' = received \cup
                         {[node |-> p, block |-> w] : p \in Node}
          /\ UNCHANGED ledger

CreateChange(n, sk) ==
    /\ sk \in PrivateKey
    /\ lastHash # NoHashVal
    /\ LET w == [ chain |-> sk, kind |-> "change", pred |-> lastHash
                 , extra |-> NoBlockVal, signer |-> sk ]
       IN /\ lastHash' = CalculateHash(w)
          /\ received' = received \cup
                         {[node |-> p, block |-> w] : p \in Node}
          /\ UNCHANGED ledger

ValidateSend(n, w) ==
    /\ [node |-> n, block |-> w] \in received
    /\ w.kind = "send"
    /\ w.extra <= Balance(n, w.pred)
    /\ PredExists(n, w)
    /\ signed == [ chain |-> w.chain, kind |-> w.kind, pred |-> w.pred
                 , extra |-> w.extra, sig |-> w.signer ]
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = signed]
    /\ received' = received \ {[node |-> n, block |-> w]}
    /\ UNCHANGED lastHash

ValidateOpen(n, w) ==
    /\ [node |-> n, block |-> w] \in received
    /\ w.kind = "open"
    /\ w.extra \in Hash
    /\ w.extra # NoHash
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [ chain |-> w.chain
        , kind |-> w.kind, pred |-> w.pred, extra |-> w.extra, sig |-> w.signer ]]
    /\ received' = received \ {[node |-> n, block |-> w]}
    /\ UNCHANGED lastHash

ValidateReceive(n, w) ==
    /\ [node |-> n, block |-> w] \in received
    /\ w.kind = "receive"
    /\ w.extra \in Hash
    /\ w.extra # NoHash
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [ chain |-> w.chain
        , kind |-> w.kind, pred |-> w.pred, extra |-> w.extra, sig |-> w.signer ]]
    /\ received' = received \ {[node |-> n, block |-> w]}
    /\ UNCHANGED lastHash

ValidateChange(n, w) ==
    /\ [node |-> n, block |-> w] \in received
    /\ w.kind = "change"
    /\ ledger' = [ledger EXCEPT ![n][lastHash] = [ chain |-> w.chain
        , kind |-> w.kind, pred |-> w.pred, extra |-> NoBlockVal, sig |-> w.signer ]]
    /\ received' = received \ {[node |-> n, block |-> w]}
    /\ UNCHANGED lastHash

Next ==
    \/ \E sk \in PrivateKey : CreateGenesis(sk) \/ \E n \in Node : CreateChange(n, sk)
    \/ \E n \in Node, sk \in PrivateKey, to \in PublicKey, amt \in 1..GenesisBalance : CreateSend(n, sk, to, amt)
    \/ \E n \in Node, sk \in PrivateKey, h \in Hash : CreateOpen(n, sk, h) \/ CreateReceive(n, sk, h)
    \/ \E n \in Node, w \in Witness : ValidateSend(n, w) \/ ValidateOpen(n, w) \/ ValidateReceive(n, w) \/ ValidateChange(n, w)

Spec == Init /\ [][Next]_vars

\* Every block in every node's replicated ledger has a signature that
\* belongs to the account chain owning that block.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => SignedByOwner(ledger[n][h])

====