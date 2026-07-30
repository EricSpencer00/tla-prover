---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES
    lastHash, ledger, received

\* The block-struct is a record of fields that all block types share. Each
\* block also carries a blockType tag so that type-specific validation rules
\* can be applied during confirmation.
BlockStruct == [account : PublicKey,
                prevHash : Hash \cup {NoHash},
                openPrev : Hash \cup {NoBlock},
                receivePrev : Hash \cup {NoBlock},
                recvHash : Hash \cup {NoBlock},
                amt : 0..GenesisBalance,
                blockType : {"genesis", "send", "open", "receive", "change"},
                signer : PrivateKey]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> BlockStruct \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

\* The genesis account is the sole source of coins, and its chain starts at
\* NoHash. No hashes exist initially.
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* Chain traversal; needed for balance checking during block creation.
\* runChain walks the chain backwards from a given hash, yielding the head
\* hash of the chain and the number of steps back to it.
Recursive runChain(_h) ==
    IF _h = NoHash THEN <<NoHash, 0>>
    ELSE LET prevRec == runChain(ledger[CHOOSE n \in Node : ledger[n][_h] # NoBlockVal].prevHash)
         IN <<IF prevRec[1] = NoHash THEN _h ELSE prevRec[1], prevRec[2] + 1>>

\* Sum balances by walking every account's longest chain and tallying the
\* send-amount fields all the way back to the genesis block.
Recursive sumBalances(_hash) ==
    IF _hash = NoHash THEN 0
    ELSE LET block == CHOOSE n \in Node : ledger[n][_hash] # NoBlockVal
         IN IF block.blockType = "send" THEN block.amt + sumBalances(block.prevHash)
            ELSE sumBalances(block.prevHash)

OnChain(_hash) == runChain(_hash)[1] # NoHash

\* Balance of the genesis account: the genesis balance minus the total sent
\* on every chain (a simple ejection model, not a real ledger).
GenesisAccountBalance ==
    IF lastHash = NoHash THEN GenesisBalance
    ELSE GenesisBalance - sumBalances(lastHash)

BlockBalance(_hash) ==
    IF _hash = NoHash THEN GenesisBalance
    ELSE LET block == CHOOSE n \in Node : ledger[n][_hash] # NoBlockVal
         IN IF block.blockType = "send" THEN block.amt ELSE 0

ValidSig(_block) == block.account = PublicKey[block.signer]

CreateGenesisBlock ==
    /\ lastHash = NoHash
    /\ \E pk \in PrivateKey :
        /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = NoHash THEN
                                            [account |-> PublicKey[pk],
                                             prevHash |-> NoHash,
                                             openPrev |-> NoBlock,
                                             receivePrev |-> NoBlock,
                                             recvHash |-> NoBlock,
                                             amt |-> GenesisBalance,
                                             blockType |-> "genesis",
                                             signer |-> pk]
                                        ELSE ledger[n][h]]]
    /\ lastHash' = NoHash
    /\ received' = received

CreateSendBlock ==
    /\ \E src \in Node, dst \in PublicKey, amt \in 1..GenesisBalance :
        /\ GenesisAccountBalance >= amt
        /\ LET block == [account |-> PublicKey[CHOOSE pk \in PrivateKey : ledger[src][lastHash] # NoBlockVal /\ PublicKey[pk] = ledger[src][lastHash].account],
                         prevHash |-> lastHash,
                         openPrev |-> NoBlock,
                         receivePrev |-> NoBlock,
                         recvHash |-> NoBlock,
                         amt |-> amt,
                         blockType |-> "send",
                         signer |-> CHOOSE pk \in PrivateKey : PublicKey[pk] = ledger[src][lastHash].account]
           IN /\ ledger' = [n \in Node |-> [h \in Hash |-> IF ledger[n][h] = NoBlockVal /\ h = block.prevHash
                                                   THEN block
                                                   ELSE ledger[n][h]]]
              /\ lastHash' = block.prevHash
              /\ received' = [n \in Node |-> received[n] \cup {block.prevHash}]
    /\ UNCHANGED <<>>

CreateOpenBlock ==
    /\ \E src \in Node, dst \in PublicKey :
        /\ \E h \in Hash :
            /\ ledger[src][h] # NoBlockVal
            /\ ledger[src][h].recvHash = NoBlock
            /\ \E a \in Node :
                /\ ledger[a][h] # NoBlockVal
                /\ ledger[a][h].account = dst
                /\ BlockBalance(h) >= 0
                /\ OnChain(h)
                /\ LET block == [account |-> dst,
                                 prevHash |-> NoHash,
                                 openPrev |-> h,
                                 receivePrev |-> NoBlock,
                                 recvHash |-> NoBlock,
                                 amt |-> BlockBalance(h),
                                 blockType |-> "open",
                                 signer |-> CHOOSE pk \in PrivateKey : PublicKey[pk] = ledger[a][h].account]
                   IN /\ ledger' = [n \in Node |-> [g \in Hash |-> IF ledger[n][g] = NoBlockVal /\ g = block.prevHash
                                                       THEN block
                                                       ELSE ledger[n][g]]]
                      /\ lastHash' = block.prevHash
                      /\ received' = [n \in Node |-> received[n] \cup {block.prevHash}]
    /\ UNCHANGED <<>>

CreateReceiveBlock ==
    /\ \E src \in Node, dst \in PublicKey :
        /\ \E h \in Hash :
            /\ ledger[src][h] # NoBlockVal
            /\ ledger[src][h].recvHash = NoBlock
            /\ ledger[src][h].account = dst
            /\ OnChain(h)
            /\ \E a \in Node :
                /\ ledger[a][lastHash] # NoBlockVal
                /\ LET block == [account |-> dst,
                                 prevHash |-> lastHash,
                                 openPrev |-> NoBlock,
                                 receivePrev |-> h,
                                 recvHash |-> NoBlock,
                                 amt |-> BlockBalance(h),
                                 blockType |-> "receive",
                                 signer |-> CHOOSE pk \in PrivateKey : PublicKey[pk] = ledger[a][lastHash].account]
                   IN /\ ledger' = [n \in Node |-> [g \in Hash |-> IF ledger[n][g] = NoBlockVal /\ g = block.prevHash
                                                       THEN block
                                                       ELSE ledger[n][g]]]
                      /\ lastHash' = block.prevHash
                      /\ received' = [n \in Node |-> received[n] \cup {block.prevHash}]
    /\ UNCHANGED <<>>

CreateChangeRepresentativeBlock ==
    /\ \E src \in Node :
        /\ \E a \in Node :
            /\ ledger[a][lastHash] # NoBlockVal
            /\ LET block == [account |-> ledger[a][lastHash].account,
                             prevHash |-> lastHash,
                             openPrev |-> NoBlock,
                             receivePrev |-> NoBlock,
                             recvHash |-> NoBlock,
                             amt |-> 0,
                             blockType |-> "change",
                             signer |-> CHOOSE pk \in PrivateKey : PublicKey[pk] = ledger[a][lastHash].account]
               IN /\ ledger' = [n \in Node |-> [g \in Hash |-> IF ledger[n][g] = NoBlockVal /\ g = block.prevHash
                                                   THEN block
                                                   ELSE ledger[n][g]]]
                  /\ lastHash' = block.prevHash
                  /\ received' = [n \in Node |-> received[n] \cup {block.prevHash}]
    /\ UNCHANGED <<>>

\* Confirmation validates signatures, checks ordering, and prevents a
\* send block from being claimed by two different accounts at once.
ConfirmBlock ==
    /\ \E src \in Node, h \in Hash :
        /\ h \in received[src]
        /\ ledger[src][h] # NoBlockVal
        /\ LET block == ledger[src][h]
           IN /\ ValidSig(block)
              /\ (block.blockType = "send" => block.prevHash # NoHash /\ ledger[src][block.prevHash] # NoBlockVal)
              /\ (block.blockType = "open" => block.openPrev # NoBlock /\ ledger[src][block.openPrev] # NoBlockVal)
              /\ (block.blockType = "receive" =>
                  /\ block.receivePrev # NoBlock /\ ledger[src][block.receivePrev] # NoBlockVal
                  /\ block.prevHash # NoHash /\ ledger[src][block.prevHash] # NoBlockVal
                  /\ \A n \in Node : ledger[n][block.receivePrev] = NoBlockVal \/ ledger[n][block.receivePrev].recvHash = NoBlock \/ ledger[n][block.receivePrev].recvHash = h)
              /\ ledger' = [n \in Node |-> [g \in Hash |-> IF g = h THEN block ELSE ledger[n][g]]]
              /\ received' = [n \in Node |-> IF n = src THEN received[n] \ {h} ELSE received[n]]
    /\ UNCHANGED <<lastHash>>

Next ==
    \/ CreateGenesisBlock
    \/ CreateSendBlock
    \/ CreateOpenBlock
    \/ CreateReceiveBlock
    \/ CreateChangeRepresentativeBlock
    \/ ConfirmBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* Every block in every ledger copy must be properly signed by the account
\* that owns the chain it sits on.
SafetyInvariant ==
    \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ValidSig(ledger[n][h])

====