---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel value meaning "no hash"
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Natural number: total supply in genesis block
    NoBlockVal,      \* Sentinel block meaning "empty"
    CalculateHash,   \* Abstract hash function
    NoHash,          \* Alias for NoHashVal (required by cfg)
    NoBlock          \* Alias for NoBlockVal (required by cfg)

\* ==== Types ====
BLOCKTYPE == {"Genesis", "Send", "Open", "Receive", "Change"}

BLOCK == [type          : BLOCKTYPE,
          hash          : Hash,
          prevHash      : Hash,
          src           : PublicKey,   \* sender (or self for non‑send)
          dst           : PublicKey,   \* recipient (or self)
          amount        : Nat,
          representative: PublicKey,
          signature     : {0,1}^512,   \* abstract signature
          ownerPubKey   : PublicKey]

\* ==== State variables ====
VARIABLES
    lastHash,          \* the most recent block hash (or NoHashVal)
    ledger,            \* [Node -> [Hash -> BLOCK \/ NoBlockVal]]
    received           \* [Node -> SUBSET Hash]

\* ==== Helper functions ==== 
\* The mapping from private to public keys is given as a constant function.
\* For simplicity we treat it as an uninterpreted relation.
PrivateKeyToPublic \in [PrivateKey -> PublicKey]

OwnerOfHash(h) == 
    IF h = NoHashVal THEN NoHashVal
    ELSE
        CHOOSE n \in Node :
            ledger[n][h] # NoBlockVal

\* Compute balance of an account by traversing its chain.
BalanceFromChain(acc, h) ==
    IF h = NoHashVal THEN 0
    ELSE
        LET blk == ledger[Node][h] IN
        IF blk.type = "Genesis" THEN GenesisBalance
        ELSE IF blk.type = "Send" THEN BalanceFromChain(acc, blk.prevHash) - blk.amount
        ELSE IF blk.type = "Receive" THEN BalanceFromChain(acc, blk.prevHash) + blk.amount
        ELSE IF blk.type = "Open"   THEN blk.amount
        ELSE IF blk.type = "Change" THEN BalanceFromChain(acc, blk.prevHash)
        ELSE 0

\* ==== Initial state ==== 
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ==== Actions ==== 

CreateGenesis ==
    /\ \E node \in Node :
        /\ \E pk \in PublicKey :
            /\ \E sk \in PrivateKey :
                /\ PrivateKeyToPublic[sk] = pk
                /\ lastHash = NoHashVal
                /\ LET genBlk == [type          |-> "Genesis",
                                 hash          |-> CalculateHash([type |-> "Genesis",
                                                                    prevHash |-> NoHashVal,
                                                                    src      |-> pk,
                                                                    dst      |-> pk,
                                                                    amount   |-> GenesisBalance,
                                                                    representative |-> pk,
                                                                    signature|-> <<>>],
                                                         NoHashVal),
                                 prevHash      |-> NoHashVal,
                                 src           |-> pk,
                                 dst           |-> pk,
                                 amount        |-> GenesisBalance,
                                 representative|-> pk,
                                 signature     |-> <<>>,
                                 ownerPubKey   |-> pk] 
                IN
                /\ lastHash' = genBlk.hash
                /\ ledger' = [n \in Node |-> 
                                [h \in Hash |-> 
                                    IF h = genBlk.hash THEN genBlk ELSE NoBlockVal]]
                /\ received' = [n \in Node |-> {}]
                /\ UNCHANGED <<>> 
    /\ UNCHANGED <<>>

CreateSend(node, sk, toPub, amt) ==
    /\ node \in Node
    /\ sk \in PrivateKey
    /\ PrivateKeyToPublic[sk] = srcPub
    /\ srcPub \in PublicKey
    /\ toPub \in PublicKey
    /\ amt \in Nat
    /\ LET prev == 
            CHOOSE h \in Hash : ledger[node][h] # NoBlockVal 
                /\ ledger[node][h].type \in {"Genesis", "Send", "Receive", "Change"}
                /\ ledger[node][h].ownerPubKey = srcPub
                /\ ~(\E blk \in DOMAIN ledger[node] : blk.type = "Send" /\ blk.prevHash = h /\ blk.amount > amt)
       IN
    /\ BalanceFromChain(srcPub, prev) >= amt
    /\ LET newHash == CalculateHash([type |-> "Send",
                                     prevHash |-> prev,
                                     src      |-> srcPub,
                                     dst      |-> toPub,
                                     amount   |-> amt,
                                     representative |-> srcPub,
                                     signature|-> <<>>],
                                    prev)
       IN
    /\ LET newBlk == [type          |-> "Send",
                      hash          |-> newHash,
                      prevHash      |-> prev,
                      src           |-> srcPub,
                      dst           |-> toPub,
                      amount        |-> amt,
                      representative|-> srcPub,
                      signature     |-> <<>>,
                      ownerPubKey   |-> srcPub]
       IN
    /\ lastHash' = newHash
    /\ ledger' = [n \in Node |-> 
                    [h \in Hash |-> 
                        IF h = newHash THEN newBlk ELSE ledger[n][h]]]
    /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED <<>>

CreateOpen(node, sk, srcSendHash) ==
    /\ node \in Node
    /\ sk \in PrivateKey
    /\ PrivateKeyToPublic[sk] = dstPub
    /\ srcSendHash \in Hash
    /\ ledger[node][srcSendHash].type = "Send"
    /\ ledger[node][srcSendHash].dst = dstPub
    /\ ledger[node][srcSendHash].ownerPubKey = srcPub
    /\ LET amount == ledger[node][srcSendHash].amount IN
    /\ LET newHash == CalculateHash([type |-> "Open",
                                     prevHash |-> NoHashVal,
                                     src      |-> srcPub,
                                     dst      |-> dstPub,
                                     amount   |-> amount,
                                     representative |-> dstPub,
                                     signature|-> <<>>],
                                    NoHashVal)
       IN
    /\ LET newBlk == [type          |-> "Open",
                      hash          |-> newHash,
                      prevHash      |-> NoHashVal,
                      src           |-> srcPub,
                      dst           |-> dstPub,
                      amount        |-> amount,
                      representative|-> dstPub,
                      signature     |-> <<>>,
                      ownerPubKey   |-> dstPub]
       IN
    /\ lastHash' = newHash
    /\ ledger' = [n \in Node |-> 
                    [h \in Hash |-> 
                        IF h = newHash THEN newBlk ELSE ledger[n][h]]]
    /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED <<>>

CreateReceive(node, sk, srcSendHash) ==
    /\ node \in Node
    /\ sk \in PrivateKey
    /\ PrivateKeyToPublic[sk] = dstPub
    /\ srcSendHash \in Hash
    /\ ledger[node][srcSendHash].type = "Send"
    /\ ledger[node][srcSendHash].dst = dstPub
    /\ LET srcPub == ledger[node][srcSendHash].src
    /\ LET amount == ledger[node][srcSendHash].amount
    /\ \E prev \in Hash :
        ledger[node][prev].ownerPubKey = dstPub
        /\ ledger[node][prev].type \in {"Genesis","Open","Receive","Change","Send"}
    /\ LET newHash == CalculateHash([type |-> "Receive",
                                     prevHash |-> prev,
                                     src      |-> srcPub,
                                     dst      |-> dstPub,
                                     amount   |-> amount,
                                     representative |-> dstPub,
                                     signature|-> <<>>],
                                    prev)
       IN
    /\ LET newBlk == [type          |-> "Receive",
                      hash          |-> newHash,
                      prevHash      |-> prev,
                      src           |-> srcPub,
                      dst           |-> dstPub,
                      amount        |-> amount,
                      representative|-> dstPub,
                      signature     |-> <<>>,
                      ownerPubKey   |-> dstPub]
       IN
    /\ lastHash' = newHash
    /\ ledger' = [n \in Node |-> 
                    [h \in Hash |-> 
                        IF h = newHash THEN newBlk ELSE ledger[n][h]]]
    /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED <<>>

CreateChange(node, sk, newRep) ==
    /\ node \in Node
    /\ sk \in PrivateKey
    /\ PrivateKeyToPublic[sk] = ownerPub
    /\ newRep \in PublicKey
    /\ \E prev \in Hash :
        ledger[node][prev].ownerPubKey = ownerPub
        /\ ledger[node][prev].type \in {"Genesis","Open","Receive","Change","Send"}
    /\ LET newHash == CalculateHash([type |-> "Change",
                                     prevHash |-> prev,
                                     src      |-> ownerPub,
                                     dst      |-> ownerPub,
                                     amount   |-> 0,
                                     representative |-> newRep,
                                     signature|-> <<>>],
                                    prev)
       IN
    /\ LET newBlk == [type          |-> "Change",
                      hash          |-> newHash,
                      prevHash      |-> prev,
                      src           |-> ownerPub,
                      dst           |-> ownerPub,
                      amount        |-> 0,
                      representative|-> newRep,
                      signature     |-> <<>>,
                      ownerPubKey   |-> ownerPub]
       IN
    /\ lastHash' = newHash
    /\ ledger' = [n \in Node |-> 
                    [h \in Hash |-> 
                        IF h = newHash THEN newBlk ELSE ledger[n][h]]]
    /\ received' = [n \in Node |-> received[n] \cup {newHash}]
    /\ UNCHANGED <<>>

ProcessBlock(node, h) ==
    /\ node \in Node
    /\ h \in received[node]
    /\ ledger[node][h] = NoBlockVal
    /\ LET blk == CHOOSE b \in DOMAIN ledger[Node] : ledger[Node][b].hash = h
       IN
    /\ /\ blk.signature = <<>>   \* abstract signature always accepted
       /\* verify referenced previous block exists */
       (blk.prevHash = NoHashVal \/ ledger[node][blk.prevHash] # NoBlockVal)
    /\ ledger' = [n \in Node |-> 
                    [hh \in Hash |-> 
                        IF hh = h THEN blk ELSE ledger[n][hh]]]
    /\ received' = [n \in Node |-> received[n] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E node \in Node, sk \in PrivateKey, toPub \in PublicKey, amt \in Nat :
          CreateSend(node, sk, toPub, amt)
    \/ \E node \in Node, sk \in PrivateKey, srcSendHash \in Hash :
          CreateOpen(node, sk, srcSendHash)
    \/ \E node \in Node, sk \in PrivateKey, srcSendHash \in Hash :
          CreateReceive(node, sk, srcSendHash)
    \/ \E node \in Node, sk \in PrivateKey, newRep \in PublicKey :
          CreateChange(node, sk, newRep)
    \/ \E node \in Node, h \in received[node] :
          ProcessBlock(node, h)
    \/ CreateGenesis

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ==== Invariants ==== 

TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHashVal}
    /\ ledger \in [Node -> [Hash -> (BLOCK \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

BlockSigValid(blk) ==
    blk.signature = <<>> /\ blk.ownerPubKey = PrivateKeyToPublic[CHOOSE sk \in PrivateKey : PrivateKeyToPublic[sk] = blk.ownerPubKey]

SafetyInvariant ==
    /\ \A n \in Node :
          \A h \in Hash :
              IF ledger[n][h] # NoBlockVal THEN BlockSigValid(ledger[n][h]) ELSE TRUE

\* ==== Specification entry point ====
vars == <<lastHash, ledger, received>>

====