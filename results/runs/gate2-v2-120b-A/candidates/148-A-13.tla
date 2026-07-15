---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,                \* universe of possible block hashes
    NoHashVal,           \* sentinel value meaning "no hash yet"
    PrivateKey,          \* universe of private keys
    PublicKey,           \* universe of public keys
    Node,                \* set of network nodes
    GenesisBalance,      \* total supply, a natural number
    NoBlockVal,          \* sentinel meaning "no block stored"
    CalculateHash,       \* abstract hash function: [Data -> Hash]
    NoHash,              \* alias for NoHashVal (for readability)
    NoBlock              \* alias for NoBlockVal (for readability)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

Block ==
    [ type          : BlockType,
      prevHash      : Hash \/ {NoHash},
      srcPubKey     : PublicKey \/ {<<>>},   \* <<>> means “none”
      dstPubKey     : PublicKey \/ {<<>>},
      amount        : Nat,
      representative: PublicKey \/ {<<>>},
      signature     : ""                    \* dummy placeholder; actual sig not modeled
    ]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,        \* the latest block hash known globally
    ledger,          \* [n \in Node -> [h \in Hash -> Block \/ {NoBlock}]]
    received         \* [n \in Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Ownership mapping and the set of keys for each node
NodeKeys == [n \in Node |-> CHOOSE pk \in PrivateKey : TRUE]   \* each node owns exactly one private key
PubOf   == [pk \in PrivateKey |-> CHOOSE pk2 \in PublicKey : TRUE]  \* abstract mapping

\* Balance of an account obtained by walking its chain
Balance(node, h) ==
    IF h = NoHash THEN 0
    ELSE
        LET blk == ledger[node][h] IN
        CASE blk.type = "Genesis"    -> blk.amount
          [] blk.type = "Send"      -> Balance(node, blk.prevHash) - blk.amount
          [] blk.type = "Open"      -> blk.amount
          [] blk.type = "Receive"   -> Balance(node, blk.prevHash) + blk.amount
          [] blk.type = "ChangeRep" -> Balance(node, blk.prevHash)
          [] OTHER                 -> Balance(node, blk.prevHash)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash               \* can only happen once
    /\ \E pk \in PrivateKey :
        LET pub == PubOf[pk] IN
        LET blk ==
            [ type          |-> "Genesis",
              prevHash      |-> NoHash,
              srcPubKey     |-> pub,
              dstPubKey     |-> <<>>,
              amount        |-> GenesisBalance,
              representative|-> pub,
              signature     |-> "sig" ] IN
        LET newHash == CalculateHash[blk] IN
        /\ newHash \in Hash
        /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![newHash] = blk]
        /\ lastHash' = newHash
        /\ UNCHANGED received

CreateSend(sender) ==
    /\ sender \in Node
    /\ \E prevBlk \in (ledger[sender]) :
        /\ prevBlk # NoBlock
        LET prevHash == CHOOSE h \in Hash : ledger[sender][h] = prevBlk IN
        LET bal == Balance(sender, prevHash) IN
        \E amount \in Nat :
            /\ amount > 0
            /\ amount <= bal
            /\ \E dst \in PublicKey :
                LET blk ==
                    [ type          |-> "Send",
                      prevHash      |-> prevHash,
                      srcPubKey     |-> PubOf[NodeKeys[sender]],
                      dstPubKey     |-> dst,
                      amount        |-> amount,
                      representative|-> PubOf[NodeKeys[sender]],
                      signature     |-> "sig"] IN
                LET newHash == CalculateHash[blk] IN
                /\ newHash \in Hash
                /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![newHash] = blk]
                /\ lastHash' = newHash
                /\ received' = [n \in Node |-> received[n] \cup {newHash}]
                /\ UNCHANGED <<>>

CreateOpen(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET blk == ledger[node][h] IN
        /\ blk.type = "Send"
        /\ blk.dstPubKey = PubOf[NodeKeys[node]]
        LET openBlk ==
            [ type          |-> "Open",
              prevHash      |-> NoHash,
              srcPubKey     |-> PubOf[NodeKeys[node]],
              dstPubKey     |-> <<>>,
              amount        |-> blk.amount,
              representative|-> PubOf[NodeKeys[node]],
              signature     |-> "sig"] IN
        LET newHash == CalculateHash[openBlk] IN
        /\ newHash \in Hash
        /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![newHash] = openBlk]
        /\ received' = [node |-> received[node] \ {h},
                       n \in Node \ {node} |-> received[n]]
        /\ UNCHANGED <<lastHash>>

CreateReceive(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET recvBlk == ledger[node][h] IN
        /\ recvBlk.type = "Send"
        /\ recvBlk.dstPubKey = PubOf[NodeKeys[node]]
        /\ \E prevHash \in Hash :
            LET prevBlk == ledger[node][prevHash] IN
            prevBlk # NoBlock
            /\ (prevBlk.type # "Open" => prevBlk.type \in {"Send","Receive","ChangeRep","Genesis"})
            LET rcvBlk ==
                [ type          |-> "Receive",
                  prevHash      |-> prevHash,
                  srcPubKey     |-> recvBlk.srcPubKey,
                  dstPubKey     |-> PubOf[NodeKeys[node]],
                  amount        |-> recvBlk.amount,
                  representative|-> PubOf[NodeKeys[node]],
                  signature     |-> "sig"] IN
            LET newHash == CalculateHash[rcvBlk] IN
            /\ newHash \in Hash
            /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![newHash] = rcvBlk]
            /\ received' = [node |-> received[node] \ {h},
                           n \in Node \ {node} |-> received[n]]
            /\ UNCHANGED <<lastHash>>

CreateChangeRep(node) ==
    /\ node \in Node
    /\ \E prevHash \in Hash :
        LET prevBlk == ledger[node][prevHash] IN
        prevBlk # NoBlock
        LET newRep == PubOf[NodeKeys[node]] IN
        LET chgBlk ==
            [ type          |-> "ChangeRep",
              prevHash      |-> prevHash,
              srcPubKey     |-> newRep,
              dstPubKey     |-> <<>>,
              amount        |-> 0,
              representative|-> newRep,
              signature     |-> "sig"] IN
        LET newHash == CalculateHash[chgBlk] IN
        /\ newHash \in Hash
        /\ ledger' = [n \in Node |-> ledger[n] EXCEPT ![newHash] = chgBlk]
        /\ lastHash' = newHash
        /\ UNCHANGED received

Validate(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
        LET blk == ledger[node][h] IN
        /\ blk # NoBlock
        /\ blk.signature = "sig"   \* dummy check – real signatures abstracted
        /\ ledger' = ledger
        /\ received' = [node |-> received[node] \ {h},
                       n \in Node \ {node} |-> received[n]]
        /\ UNCHANGED <<lastHash>>

Next ==
    \/ CreateGenesis
    \/ \E n \in Node : CreateSend(n)
    \/ \E n \in Node : CreateOpen(n)
    \/ \E n \in Node : CreateReceive(n)
    \/ \E n \in Node : CreateChangeRep(n)
    \/ \E n \in Node : Validate(n)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \/ {NoBlock}]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] = NoBlock THEN TRUE
            ELSE ledger[n][h].signature = "sig"

\* (optional balance-sum invariant, not required by cfg but useful)
BalanceSumInvariant ==
    Let total == +\{ n \in Node : Balance(n, lastHash) } IN
    total <= GenesisBalance

=============================================================================