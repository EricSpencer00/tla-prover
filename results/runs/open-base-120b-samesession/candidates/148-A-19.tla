---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash,          \* set of possible block hashes
    NoHash,        \* sentinel hash (member of Hash)
    NoHashVal,     \* alias for NoHash (kept for compatibility with cfg)
    PrivateKey,   \* set of private keys
    PublicKey,    \* set of public keys
    Node,          \* set of network nodes
    GenesisBalance, \* total supply (natural number)
    NoBlockVal,    \* sentinel block value
    CalculateHash, \* abstract hash operator (will be overridden by CalculateHashImpl)
    NoBlock        \* alias for NoBlockVal (kept for cfg compatibility)

\* ----------------------------------------------------------------------
\* Mappings and auxiliary constants
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,          \* the most recent block hash in the system
    ledger,            \* [Node -> [Hash -> Block]]
    received,          \* [Node -> SUBSET Hash]  blocks received but not yet processed
    head               \* [Node -> Hash]        latest block of each account chain

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "Change", "None"}

Block ==
    [ type          : BlockType,
      prev          : Hash,
      account       : PublicKey,
      destination   : PublicKey,
      amount        : Nat,
      source        : Hash,
      representative: PublicKey,
      sig           : PrivateKey ]

\* Sentinel values (must belong to the declared constant sets)
NoPublicKey == CHOOSE pk \in PublicKey : TRUE
NoBlockVal == [type |-> "None",
               prev |-> NoHash,
               account |-> NoPublicKey,
               destination |-> NoPublicKey,
               amount |-> 0,
               source |-> NoHash,
               representative |-> NoPublicKey,
               sig |-> CHOOSE sk \in PrivateKey : TRUE]

\* ----------------------------------------------------------------------
\* Cryptographic assumptions
\* ----------------------------------------------------------------------
\* Mapping from private to public keys (must be a function)
PrivateToPublic \in [PrivateKey -> PublicKey]

\* Abstract hash calculation – the concrete implementation is supplied by the
\* configuration file via substitution of CalculateHash with CalculateHashImpl.
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* Signature verification
SigOK(b) == PrivateToPublic[b.sig] = b.account

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* Retrieve the latest block hash for a given node (account)
LatestHash(n) == head[n]

\* Extract the amount represented by a block (relevant for Send, Open, Receive)
BlockAmount(b) ==
    CASE b.type = "Send"   -> b.amount
         b.type = "Open"   -> b.amount
         b.type = "Receive"-> b.amount
         OTHER            -> 0

\* Determine the current balance of an account by walking its chain.
\* For the purpose of this finite model we compute it by summing amounts of
\* all blocks of type Send (negative) and Receive/Open (positive) reachable
\* from the head of the chain.
Balance(n) ==
    LET chainHashes == { h \in Hash : ledger[n][h] # NoBlockVal } IN
    LET sends   == { h \in chainHashes :
                      ledger[n][h].type = "Send" } IN
    LET recvs   == { h \in chainHashes :
                      ledger[n][h].type \in {"Receive", "Open"} } IN
    (GenesisBalance * (n = GenesisNode)) + 
        (Sum({ BlockAmount(ledger[n][h]) : h \in recvs }) -
         Sum({ BlockAmount(ledger[n][h]) : h \in sends }))

\* Identify the node that owns a given private key
OwnerNode(sk) == CHOOSE n \in Node : OwnedKey[n] = sk

\* The node that creates the genesis block (chosen nondeterministically)
GenesisNode == CHOOSE n \in Node : TRUE

\* Mapping from nodes to their owned private key (assumed total function)
OwnedKey \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ head = [n \in Node |-> NoHash]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Create Genesis Block (once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ let n == GenesisNode
       pk == OwnedKey[n]
       pub == PrivateToPublic[pk] in
    /\ let blk == [ type          |-> "Genesis",
                   prev          |-> NoHash,
                   account       |-> pub,
                   destination   |-> NoPublicKey,
                   amount        |-> GenesisBalance,
                   source        |-> NoHash,
                   representative|-> NoPublicKey,
                   sig           |-> pk ] in
    /\ let h == CalculateHash(blk, NoHash) in
    /\ lastHash' = h
    /\ ledger' = [node \in Node |-> ledger[node] \oplus [h |-> blk]]
    /\ received' = [node \in Node |-> {}]
    /\ head' = [head EXCEPT ![n] = h]
    /\ UNCHANGED << >>

\* 2. Create Send Block
CreateSend ==
    /\ let n == OwnerNode(sk) in
       sk \in PrivateKey /\ pk == OwnedKey[n] /\ pub == PrivateToPublic[pk] in
    /\ let prevHash == LatestHash(n) in
       prevHash # NoHash in
    /\ let maxAmt == Balance(n) in
       maxAmt > 0 in
    /\ let destPub == PublicKey \ {pub} in
       \E d \in destPub : TRUE in
    /\ let amt \in 1..maxAmt : TRUE in
    /\ let blk == [ type          |-> "Send",
                   prev          |-> prevHash,
                   account       |-> pub,
                   destination   |-> d,
                   amount        |-> amt,
                   source        |-> NoHash,
                   representative|-> NoPublicKey,
                   sig           |-> sk ] in
    /\ let h == CalculateHash(blk, prevHash) in
    /\ lastHash' = h
    /\ ledger' = [node \in Node |-> ledger[node] \oplus [h |-> blk]]
    /\ received' = [node \in Node |-> {}]
    /\ head' = [head EXCEPT ![n] = h]
    /\ UNCHANGED << >>

\* 3. Create Open Block (opens a new account based on a received send)
CreateOpen ==
    /\ \E n \in Node :
         LET sk == OwnedKey[n] IN
         LET pub == PrivateToPublic[sk] IN
         /\ head[n] = NoHash          \* account not yet opened
         /\ \E sHash \in Hash :
                /\ ledger[n][sHash] # NoBlockVal
                /\ ledger[n][sHash].type = "Send"
                /\ ledger[n][sHash].destination = pub
                /\ let amt == ledger[n][sHash].amount in
                   /\ let blk == [ type          |-> "Open",
                                   prev          |-> NoHash,
                                   account       |-> pub,
                                   destination   |-> NoPublicKey,
                                   amount        |-> amt,
                                   source        |-> sHash,
                                   representative|-> NoPublicKey,
                                   sig           |-> sk ] in
                   /\ let h == CalculateHash(blk, NoHash) in
                   /\ lastHash' = h
                   /\ ledger' = [node \in Node |-> ledger[node] \oplus [h |-> blk]]
                   /\ received' = [node \in Node |-> {}]
                   /\ head' = [head EXCEPT ![n] = h]
    /\ UNCHANGED << >>

\* 4. Create Receive Block
CreateReceive ==
    /\ \E n \in Node :
         LET sk == OwnedKey[n] IN
         LET pub == PrivateToPublic[sk] IN
         LET prevHash == LatestHash(n) IN
         prevHash # NoHash /\ 
         /\ \E sHash \in Hash :
                /\ ledger[n][sHash] # NoBlockVal
                /\ ledger[n][sHash].type = "Send"
                /\ ledger[n][sHash].destination = pub
                /\ \A r \in Hash :
                      ledger[n][r].type = "Receive" => ledger[n][r].source # sHash
                /\ let amt == ledger[n][sHash].amount in
                   LET blk == [ type          |-> "Receive",
                                prev          |-> prevHash,
                                account       |-> pub,
                                destination   |-> NoPublicKey,
                                amount        |-> amt,
                                source        |-> sHash,
                                representative|-> NoPublicKey,
                                sig           |-> sk ] IN
                   LET h == CalculateHash(blk, prevHash) IN
                   lastHash' = h
                   /\ ledger' = [node \in Node |-> ledger[node] \oplus [h |-> blk]]
                   /\ received' = [node \in Node |-> {}]
                   /\ head' = [head EXCEPT ![n] = h]
    /\ UNCHANGED << >>

\* 5. Create Change Representative Block
CreateChange ==
    /\ \E n \in Node :
         LET sk == OwnedKey[n] IN
         LET pub == PrivateToPublic[sk] IN
         LET prevHash == LatestHash(n) IN
         prevHash # NoHash /\ 
         /\ \E repPub \in PublicKey :
                repPub # pub /\ 
                LET blk == [ type          |-> "Change",
                             prev          |-> prevHash,
                             account       |-> pub,
                             destination   |-> NoPublicKey,
                             amount        |-> 0,
                             source        |-> NoHash,
                             representative|-> repPub,
                             sig           |-> sk ] IN
                LET h == CalculateHash(blk, prevHash) IN
                lastHash' = h
                /\ ledger' = [node \in Node |-> ledger[node] \oplus [h |-> blk]]
                /\ received' = [node \in Node |-> {}]
                /\ head' = [head EXCEPT ![n] = h]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, head>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ head \in [Node -> Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal
            THEN SigOK(ledger[n][h])
            ELSE TRUE

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====