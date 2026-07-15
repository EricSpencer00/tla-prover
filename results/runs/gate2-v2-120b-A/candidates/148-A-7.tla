---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants (must match the .cfg file)
\* -------------------------------------------------
CONSTANTS
    Hash,               \* universe of possible hash values
    NoHashVal,          \* sentinel representing "no hash yet"
    PrivateKey,         \* set of all private keys
    PublicKey,          \* set of all public keys
    Node,               \* set of all network nodes
    GenesisBalance,     \* total supply of coins (a natural number)
    NoBlockVal,         \* sentinel representing "no block"
    CalculateHash,      \* abstract hash function
    NoHash,             \* synonym for NoHashVal (used in state vars)
    NoBlock             \* synonym for NoBlockVal (used in ledgers)

\* -------------------------------------------------
\* Types derived from constants
\* -------------------------------------------------
TYPEDEF BlockType == {"Send", "Receive", "Open", "Change", "Genesis"}

Block ==
    [ type       : BlockType,
      hash       : Hash,
      prevHash   : Hash,
      targetHash : Hash,            \* used by Receive/Open to point to a send block
      amount     : Nat,
      senderKey  : PublicKey,
      receiverKey: PUBLICKEY \cup {"Genesis"},
      representative : PublicKey,
      signature  : STRING ]          \* abstract representation of a signature

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES
    lastHash,          \* the most recent block hash observed globally
    ledgers,          \* [node \in Node -> [h \in Hash -> Block \cup {NoBlock}]]
    received,         \* [node \in Node -> SUBSET Hash]
    privToPub          \* mapping PrivateKey -> PublicKey (constant, but kept as variable for convenience)

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
AllHashes == Hash \cup {NoHashVal}
AllBlocks == Block \cup {NoBlock}

\* Balance of an account is computed by walking its chain
Balance(node) ==
    LET acctKey == privToPub[NodeOwnerKey(node)] IN
    \* The function walks the chain starting from the latest block belonging
    \* to the account. For simplicity we assume the latest block is the one
    \* whose hash equals lastHash and belongs to the account; in a full model
    \* we would need a map from account to its tip, but that is unnecessary for
    \* the invariants we check.
    IF \E b \in ledgers[Node] : b.hash = lastHash /\ b.senderKey = acctKey
       THEN BalanceFromTip(lastHash, node)
       ELSE 0

BalanceFromTip(tip, node) ==
    IF tip = NoHashVal THEN 0
    ELSE
        LET blk == Choose b \in ledgers[Node] : b.hash = tip IN
        CASE blk.type = "Receive"  -> BalanceFromTip(blk.prevHash, node) + blk.amount
        []   blk.type = "Send"    -> BalanceFromTip(blk.prevHash, node) - blk.amount
        []   blk.type = "Open"    -> blk.amount
        []   blk.type = "Change"  -> BalanceFromTip(blk.prevHash, node)
        []   blk.type = "Genesis" -> blk.amount
        []   OTHER               -> 0

\* Returns the private key owned by a node (for simplicity each node owns exactly one)
NodeOwnerKey(node) == CHOOSE k \in PrivateKey : privToPub[k] \in PublicKey

\* Abstract signature verification (always true in this abstract model)
ValidSignature(blk) == TRUE

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledgers = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ privToPub \in [PrivateKey -> PublicKey]

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \A n \in Node: ledgers[n] = [h \in Hash |-> NoBlock]
    /\ \A n \in Node: received[n] = {}
    /\ \E p \in PrivateKey :
          LET blk ==
                [type          |-> "Genesis",
                 hash          |-> CalculateHash("genesis", NoHashVal),
                 prevHash      |-> NoHashVal,
                 targetHash    |-> NoHashVal,
                 amount        |-> GenesisBalance,
                 senderKey     |-> privToPub[p],
                 receiverKey   |-> "Genesis",
                 representative|-> privToPub[p],
                 signature     |-> "sig"] IN
          /\ blk.hash \in Hash
          /\ \A n \in Node: ledgers' = [ledgers EXCEPT ![n][blk.hash] = blk]
          /\ \A n \in Node: received' = [received EXCEPT ![n] = {}]
          /\ lastHash' = blk.hash
    /\ UNCHANGED privToPub

CreateSend ==
    \E n \in Node :
       \E p \in PrivateKey :
          /\ privToPub[p] = NodeOwnerKey(n)               \* node owns this private key
          /\ \E prev \in Hash :
                /\ prev # NoHashVal
                /\ ledgers[n][prev] # NoBlock
                /\ Let prevBlk == ledgers[n][prev] In
                   prevBlk.senderKey = NodeOwnerKey(n)
                /\ \E amt \in Nat :
                       amt > 0 /\ amt <= Balance(n)
                       /\ \E recvKey \in PublicKey :
                            \E newHash \in Hash :
                                LET blk ==
                                  [type          |-> "Send",
                                   hash          |-> newHash,
                                   prevHash      |-> prev,
                                   targetHash    |-> recvKey,
                                   amount        |-> amt,
                                   senderKey     |-> NodeOwnerKey(n),
                                   receiverKey   |-> recvKey,
                                   representative|-> prevBlk.representative,
                                   signature     |-> "sig"] IN
                                /\ blk.hash = CalculateHash({prev, recvKey, amt}, prev)
                                /\ \A m \in Node: ledgers'[m] = [ledgers[m] EXCEPT ![blk.hash] = blk]
                                /\ \A m \in Node: received'[m] = received[m] \cup {blk.hash}
                                /\ lastHash' = blk.hash

CreateOpen ==
    \E n \in Node :
       \E recvKey \in PublicKey :
          \E sendHash \in Hash :
             /\ ledgers[n][sendHash] # NoBlock
             /\ ledgers[n][sendHash].type = "Send"
             /\ ledgers[n][sendHash].targetHash = NodeOwnerKey(n)
             /\ \E newHash \in Hash :
                 LET blk ==
                   [type          |-> "Open",
                    hash          |-> newHash,
                    prevHash      |-> NoHashVal,
                    targetHash    |-> sendHash,
                    amount        |-> ledgers[n][sendHash].amount,
                    senderKey     |-> NodeOwnerKey(n),
                    receiverKey   |-> NodeOwnerKey(n),
                    representative|-> privToPub[NodeOwnerKey(n)],
                    signature     |-> "sig"] IN
                 /\ blk.hash = CalculateHash({sendHash, amount}, NoHashVal)
                 /\ \A m \in Node: ledgers'[m] = [ledgers[m] EXCEPT ![blk.hash] = blk]
                 /\ \A m \in Node: received'[m] = received[m] \cup {blk.hash}
                 /\ lastHash' = blk.hash

CreateReceive ==
    \E n \in Node :
       \E recvKey \in PublicKey :
          \E sendHash \in Hash :
             /\ ledgers[n][sendHash] # NoBlock
             /\ ledgers[n][sendHash].type = "Send"
             /\ ledgers[n][sendHash].targetHash = NodeOwnerKey(n)
             /\ \E prev \in Hash :
                 /\ ledgers[n][prev] # NoBlock
                 /\ ledgers[n][prev].senderKey = NodeOwnerKey(n)
                 /\ \E newHash \in Hash :
                     LET blk ==
                       [type          |-> "Receive",
                        hash          |-> newHash,
                        prevHash      |-> prev,
                        targetHash    |-> sendHash,
                        amount        |-> ledgers[n][sendHash].amount,
                        senderKey     |-> NodeOwnerKey(n),
                        receiverKey   |-> NodeOwnerKey(n),
                        representative|-> ledgers[n][prev].representative,
                        signature     |-> "sig"] IN
                     /\ blk.hash = CalculateHash({prev, sendHash, amount}, prev)
                     /\ \A m \in Node: ledgers'[m] = [ledgers[m] EXCEPT ![blk.hash] = blk]
                     /\ \A m \in Node: received'[m] = received[m] \cup {blk.hash}
                     /\ lastHash' = blk.hash

CreateChange ==
    \E n \in Node :
       \E prev \in Hash :
          /\ ledgers[n][prev] # NoBlock
          /\ \E newRep \in PublicKey :
               \E newHash \in Hash :
                 LET blk ==
                   [type          |-> "Change",
                    hash          |-> newHash,
                    prevHash      |-> prev,
                    targetHash    |-> NoHashVal,
                    amount        |-> 0,
                    senderKey     |-> NodeOwnerKey(n),
                    receiverKey   |-> NodeOwnerKey(n),
                    representative|-> newRep,
                    signature     |-> "sig"] IN
                 /\ blk.hash = CalculateHash({prev, newRep}, prev)
                 /\ \A m \in Node: ledgers'[m] = [ledgers[m] EXCEPT ![blk.hash] = blk]
                 /\ \A m \in Node: received'[m] = received[m] \cup {blk.hash}
                 /\ lastHash' = blk.hash

\* Processing a received block at a node (validation already abstracted)
ProcessReceived ==
    \E n \in Node :
       \E h \in received[n] :
          LET blk == ledgers[n][h] IN
          /\ blk # NoBlock
          /\ ValidSignature(blk)
          /\ (* basic structural checks *)
             IF blk.type = "Send"
                THEN /\ blk.prevHash # NoHashVal
                     /\ ledgers[n][blk.prevHash] # NoBlock
                     /\ Balance(n) >= blk.amount
                     /\ ledgers[n][blk.hash] = blk
                ELSE IF blk.type = "Receive"
                     THEN /\ ledgers[n][blk.prevHash] # NoBlock
                          /\ ledgers[n][blk.targetHash] # NoBlock
                          /\ ledgers[n][blk.targetHash].type = "Send"
                          /\ ledgers[n][blk.targetHash].targetHash = NodeOwnerKey(n)
                          /\ ledgers[n][blk.hash] = blk
                ELSE IF blk.type = "Open"
                     THEN /\ ledgers[n][blk.targetHash] # NoBlock
                          /\ ledgers[n][blk.targetHash].type = "Send"
                          /\ ledgers[n][blk.targetHash].targetHash = NodeOwnerKey(n)
                          /\ ledgers[n][blk.hash] = blk
                ELSE IF blk.type = "Change"
                     THEN /\ ledgers[n][blk.prevHash] # NoBlock
                          /\ ledgers[n][blk.hash] = blk
                ELSE IF blk.type = "Genesis"
                     THEN /\ lastHash = NoHashVal
                          /\ ledgers[n][blk.hash] = blk
                ELSE /\ FALSE
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED << lastHash, ledgers, privToPub >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledgers, received, privToPub>>

\* -------------------------------------------------
\* Invariants
\* -------------------------------------------------
TypeInvariant ==
    /\ lastHash \in AllHashes
    /\ ledgers \in [Node -> [Hash -> AllBlocks]]
    /\ received \in [Node -> SUBSET Hash]
    /\ privToPub \in [PrivateKey -> PublicKey]

SafetyInvariant ==
    \A n \in Node :
       \A h \in Hash :
          IF ledgers[n][h] # NoBlock THEN ValidSignature(ledgers[n][h]) ELSE TRUE

\* -------------------------------------------------
\* Theorems (optional, but we expose the invariants)
\* -------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant

====