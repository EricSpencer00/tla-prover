---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Hash,          \* Set of possible block hashes
    NoHash,        \* Sentinel hash that denotes "no previous hash"
    NoHashVal,     \* Value used in block fields when a hash is absent
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total amount of coins at genesis (a Nat)
    NoBlock,       \* Sentinel value meaning “no block stored”
    NoBlockVal,    \* Value used for a block field when there is no block
    CalculateHash, \* Abstract hash operator (will be overridden)
    PrivToPub,     \* Mapping from private to public key
    Sign           \* Abstract signing function (priv × data -> signature)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change"}

Block == [ hash          : Hash,
           prev          : Hash,
           type          : BlockType,
           account       : PublicKey,
           sig           : STRING,
           amount        : Nat,
           recipient     : PublicKey,
           source        : Hash,
           representative: PublicKey ]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the hash of the most recent block created in the system
    blocks,     \* global mapping from hash to the block (or NoBlock)
    ledger,     \* per‑node copy of the ledger: Node -> (Hash -> (Block \cup {NoBlock}))
    received    \* per‑node set of hashes that have been received but not yet processed

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Payload that is signed – in this abstract model we simply use the block type
Payload(b) == b.type

\* A block’s signature is valid iff it was produced by the private key that
\* corresponds to the block’s account public key.
ValidSignature(b) ==
    \E priv \in PrivateKey :
        /\ PrivToPub[priv] = b.account
        /\ b.sig = Sign(priv, Payload(b))

\* Amount contributed by a block to its account balance
AmtContribution(b) ==
    IF b.type = "Send"    THEN -b.amount
    ELSE IF b.type = "Receive" THEN b.amount
    ELSE IF b.type = "Genesis" THEN b.amount
    ELSE 0

\* Sum of a finite set of natural numbers (recursive definition)
Sum(S) ==
    IF S = {} THEN 0
    ELSE
        LET b == CHOOSE x \in S : TRUE IN
        AmtContribution(b) + Sum(S \ {b})

\* Balance of a public key in the (processed) blocks of the whole system
Balance(pub) ==
    LET allBlocks == { b \in UNION { ledger[n][h] : n \in Node, h \in Hash } :
                         b # NoBlock /\ b.account = pub } IN
    Sum(allBlocks)

\* The set of hashes that have been created (i.e., have a non‑sentinel block)
CreatedHashes == { h \in Hash : blocks[h] # NoBlock }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ blocks = [ h \in Hash |-> NoBlock ]
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* ---- Genesis block creation (once) ----
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E priv \in PrivateKey :
         LET pub   == PrivToPub[priv] IN
         LET gHash == CalculateHashImpl("Genesis", NoHash) IN
         LET gBlk  == [ hash          |-> gHash,
                        prev          |-> NoHash,
                        type          |-> "Genesis",
                        account       |-> pub,
                        sig           |-> Sign(priv, "Genesis"),
                        amount        |-> GenesisBalance,
                        recipient     |-> NoHashVal,
                        source        |-> NoHash,
                        representative|-> NoHashVal ] IN
         /\ lastHash' = gHash
         /\ blocks'   = [blocks EXCEPT ![gHash] = gBlk]
         /\ ledger'   = [ n \in Node |-> [ h \in Hash |-> IF h = gHash THEN gBlk ELSE NoBlock ] ]
         /\ UNCHANGED received

\* ---- Create a Send block (broadcast) ----
CreateSend ==
    /\ \E n \in Node :
         \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            (* assume node n owns priv – this link can be supplied by a constant mapping if needed *)
            /\ (* balance check *) Amount <= Balance(pub)
            /\ \E prev \in Hash :
                 /\ ledger[n][prev] # NoBlock
                 /\ ledger[n][prev].account = pub
                 /\ \E amt \in Nat :
                      /\ amt <= Balance(pub)
                      /\ \E recPub \in PublicKey :
                           LET sHash == CalculateHashImpl("Send" \o ToString(amt) \o recPub, prev) IN
                           LET sBlk  == [ hash          |-> sHash,
                                          prev          |-> prev,
                                          type          |-> "Send",
                                          account       |-> pub,
                                          sig           |-> Sign(priv, "Send"),
                                          amount        |-> amt,
                                          recipient     |-> recPub,
                                          source        |-> NoHash,
                                          representative|-> NoHashVal ] IN
                           /\ blocks'   = [blocks EXCEPT ![sHash] = sBlk]
                           /\ received' = [ node \in Node |-> received[node] \cup {sHash} ]
                           /\ UNCHANGED << lastHash, ledger >>

\* ---- Create an Open block (broadcast) ----
CreateOpen ==
    /\ \E n \in Node :
         \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            /\ \E srcHash \in Hash :
                 /\ blocks[srcHash] # NoBlock
                 /\ blocks[srcHash].type = "Send"
                 /\ blocks[srcHash].recipient = pub
                 /\ \E openHash == CalculateHashImpl("Open", srcHash) :
                       LET oBlk == [ hash          |-> openHash,
                                    prev          |-> NoHash,
                                    type          |-> "Open",
                                    account       |-> pub,
                                    sig           |-> Sign(priv, "Open"),
                                    amount        |-> 0,
                                    recipient     |-> NoHashVal,
                                    source        |-> srcHash,
                                    representative|-> NoHashVal ] IN
                       /\ blocks'   = [blocks EXCEPT ![openHash] = oBlk]
                       /\ received' = [ node \in Node |-> received[node] \cup {openHash} ]
                       /\ UNCHANGED << lastHash, ledger >>

\* ---- Create a Receive block (broadcast) ----
CreateReceive ==
    /\ \E n \in Node :
         \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            /\ \E prev \in Hash :
                 /\ ledger[n][prev] # NoBlock
                 /\ ledger[n][prev].account = pub
                 /\ \E srcHash \in Hash :
                      /\ blocks[srcHash] # NoBlock
                      /\ blocks[srcHash].type = "Send"
                      /\ blocks[srcHash].recipient = pub
                      /\ \E recvHash == CalculateHashImpl("Receive", prev) :
                           LET rBlk == [ hash          |-> recvHash,
                                         prev          |-> prev,
                                         type          |-> "Receive",
                                         account       |-> pub,
                                         sig           |-> Sign(priv, "Receive"),
                                         amount        |-> 0,
                                         recipient     |-> NoHashVal,
                                         source        |-> srcHash,
                                         representative|-> NoHashVal ] IN
                           /\ blocks'   = [blocks EXCEPT ![recvHash] = rBlk]
                           /\ received' = [ node \in Node |-> received[node] \cup {recvHash} ]
                           /\ UNCHANGED << lastHash, ledger >>

\* ---- Create a Change Representative block (broadcast) ----
CreateChange ==
    /\ \E n \in Node :
         \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            /\ \E prev \in Hash :
                 /\ ledger[n][prev] # NoBlock
                 /\ ledger[n][prev].account = pub
                 /\ \E newRep \in PublicKey :
                      LET cHash == CalculateHashImpl("Change", prev) IN
                      LET cBlk  == [ hash          |-> cHash,
                                     prev          |-> prev,
                                     type          |-> "Change",
                                     account       |-> pub,
                                     sig           |-> Sign(priv, "Change"),
                                     amount        |-> 0,
                                     recipient     |-> NoHashVal,
                                     source        |-> NoHash,
                                     representative|-> newRep ] IN
                      /\ blocks'   = [blocks EXCEPT ![cHash] = cBlk]
                      /\ received' = [ node \in Node |-> received[node] \cup {cHash} ]
                      /\ UNCHANGED << lastHash, ledger >>

\* ---- Process a received block at a node ----
ProcessBlock ==
    /\ \E n \in Node :
         /\ \E h \in received[n] :
              LET blk == blocks[h] IN
              /\ blk # NoBlock
              /\ ValidSignature(blk)
              /\ (* reference checks *) 
                 IF blk.type = "Send"   THEN blk.prev \in CreatedHashes
                 ELSE IF blk.type = "Open"   THEN blk.source \in CreatedHashes
                 ELSE IF blk.type = "Receive" THEN blk.prev \in CreatedHashes /\ blk.source \in CreatedHashes
                 ELSE IF blk.type = "Change"  THEN blk.prev \in CreatedHashes
                 ELSE TRUE
              /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
              /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
              /\ UNCHANGED << lastHash, blocks >>

\* ---- The overall next‑state relation ----
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, blocks, ledger, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ blocks \in [Hash -> (Block \cup {NoBlock})]
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlock
            THEN ValidSignature(ledger[n][h])
            ELSE TRUE

\* ----------------------------------------------------------------------
\* Concrete implementation of CalculateHash for model checking
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

====