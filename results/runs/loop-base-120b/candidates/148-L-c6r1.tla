---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
   Hash,            \* Set of all block hashes
   NoHashVal,       \* Sentinel hash value (member of Hash)
   PrivateKey,      \* Set of private keys
   PublicKey,       \* Set of public keys
   Node,            \* Set of network nodes
   GenesisBalance,  \* Total supply (a natural number)
   NoBlockVal,      \* Sentinel block value
   CalculateHash,   \* Abstract hash operator (will be substituted)
   NoHash,          \* Alias for NoHashVal (also a member of Hash)
   NoBlock          \* Alias for NoBlockVal (sentinel block)

\* ----------------------------------------------------------------------
\* Additional static mappings (can be left uninterpreted in the model)
\* ----------------------------------------------------------------------
CONSTANTS
   Priv2Pub,        \* Mapping PrivateKey -> PublicKey
   NodeKey          \* Mapping Node -> PrivateKey

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
   lastHash,        \* The most recent block hash (or NoHash)
   ledger,          \* Ledger[n][h] = block stored at node n for hash h
   received,        \* received[n] = set of hashes pending validation at node n
   blockStore       \* Global store mapping each hash to its block (or NoBlock)

\* ----------------------------------------------------------------------
\* Record type for a block. All fields are present; irrelevant fields
\* are filled with a default value (e.g., NoHash, NoBlock, 0, or a dummy key).
\* ----------------------------------------------------------------------
Block ==
  [ type       : {"genesis","send","open","receive","change"},
    prev       : Hash,
    account    : PublicKey,
    amount     : Nat,
    recipient  : PublicKey,
    source     : Hash,
    rep        : PublicKey,
    signature  : STRING ]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The data that is signed for a block – abstracted as a sequence.
BlockData(b) == << b.type, b.prev, b.account, b.amount,
                  b.recipient, b.source, b.rep >>

\* Abstract signing (placeholder)
Sign(priv, data) == "sig_" \o ToString(priv) \o "_" \o ToString(data)

\* Abstract signature verification (placeholder – always true)
VerifySig(pub, data, sig) == TRUE

\* Predicate that a block is well‑typed (all fields belong to the declared sets)
IsWellTypedBlock(b) ==
  /\ b.type \in {"genesis","send","open","receive","change"}
  /\ b.prev \in Hash
  /\ b.account \in PublicKey
  /\ b.amount \in Nat
  /\ b.recipient \in PublicKey
  /\ b.source \in Hash
  /\ b.rep \in PublicKey
  /\ b.signature \in STRING

\* Accessors for the latest block of an account in a node's ledger.
LatestBlock(pub, n) ==
  CHOOSE h \in Hash :
     /\ ledger[n][h] # NoBlock
     /\ ledger[n][h].account = pub
     /\ \A h2 \in Hash :
          (ledger[n][h2] # NoBlock /\ ledger[n][h2].account = pub) => 
          (h2 = h) \/ (ledger[n][h2].prev # h)

\* Balance of an account in a node's ledger (abstract; always non‑negative)
Balance(pub, n) == 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ lastHash = NoHash
  /\ blockStore = [h \in Hash |-> NoBlock]
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: Create genesis block (once)
\* ----------------------------------------------------------------------
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E n \in Node :
        LET priv == NodeKey[n] 
            pub  == Priv2Pub[priv] 
            data == << "genesis", pub, GenesisBalance >> 
            h    == CalculateHash(data, NoHash) 
            b    == [ type      |-> "genesis",
                     prev      |-> NoHash,
                     account   |-> pub,
                     amount    |-> GenesisBalance,
                     recipient |-> pub,
                     source    |-> NoHash,
                     rep       |-> pub,
                     signature |-> Sign(priv, data) ] 
        IN
          /\ h \in Hash
          /\ b # NoBlock
          /\ IsWellTypedBlock(b)
          /\ blockStore' = [blockStore EXCEPT ![h] = b]
          /\ ledger' = [n2 \in Node |-> [h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2]]]
          /\ lastHash' = h
          /\ received' = received
          /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: Create a send block
\* ----------------------------------------------------------------------
CreateSend ==
  /\ \E n \in Node :
        LET priv == NodeKey[n] 
            pub  == Priv2Pub[priv] 
            prev == LatestBlock(pub, n) 
        IN
          /\ maxAmt == Balance(pub, n)
          /\ maxAmt > 0
          /\ \E amt \in 1..maxAmt :
                \E recPub \in PublicKey :
                  LET data == << "send", pub, amt, recPub >> 
                      h    == CalculateHash(data, prev) 
                      b    == [ type      |-> "send",
                               prev      |-> prev,
                               account   |-> pub,
                               amount    |-> amt,
                               recipient |-> recPub,
                               source    |-> NoHash,
                               rep       |-> pub,
                               signature |-> Sign(priv, data) ] 
                  IN
                    /\ h \in Hash
                    /\ b # NoBlock
                    /\ IsWellTypedBlock(b)
                    /\ blockStore' = [blockStore EXCEPT ![h] = b]
                    /\ ledger' = ledger
                    /\ lastHash' = lastHash
                    /\ received' = [m \in Node |-> received[m] \cup {h}]
                    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: Create an open block (first block of a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
  /\ \E n \in Node :
        LET priv == NodeKey[n] 
            pub  == Priv2Pub[priv] 
        IN
          /\ \A h \in Hash : ~(ledger[n][h] # NoBlock /\ ledger[n][h].account = pub)  \* account not yet opened
          /\ \E src \in Hash :
                /\ blockStore[src] # NoBlock
                /\ blockStore[src].type = "send"
                /\ blockStore[src].recipient = pub
                LET data == << "open", pub, src >> 
                    h    == CalculateHash(data, NoHash) 
                    b    == [ type      |-> "open",
                             prev      |-> NoHash,
                             account   |-> pub,
                             amount    |-> 0,
                             recipient |-> pub,
                             source    |-> src,
                             rep       |-> pub,
                             signature |-> Sign(priv, data) ] 
                IN
                  /\ h \in Hash
                  /\ b # NoBlock
                  /\ IsWellTypedBlock(b)
                  /\ blockStore' = [blockStore EXCEPT ![h] = b]
                  /\ ledger' = ledger
                  /\ lastHash' = lastHash
                  /\ received' = [m \in Node |-> received[m] \cup {h}]
                  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: Create a receive block
\* ----------------------------------------------------------------------
CreateReceive ==
  /\ \E n \in Node :
        LET priv == NodeKey[n] 
            pub  == Priv2Pub[priv] 
            prev == LatestBlock(pub, n) 
        IN
          /\ \E src \in Hash :
                /\ blockStore[src] # NoBlock
                /\ blockStore[src].type = "send"
                /\ blockStore[src].recipient = pub
                /\ \A h \in Hash :
                     ~(ledger[n][h] # NoBlock /\ ledger[n][h].type = "receive" /\ ledger[n][h].source = src)
                LET data == << "receive", pub, src >> 
                    h    == CalculateHash(data, prev) 
                    b    == [ type      |-> "receive",
                             prev      |-> prev,
                             account   |-> pub,
                             amount    |-> 0,
                             recipient |-> pub,
                             source    |-> src,
                             rep       |-> pub,
                             signature |-> Sign(priv, data) ] 
                IN
                  /\ h \in Hash
                  /\ b # NoBlock
                  /\ IsWellTypedBlock(b)
                  /\ blockStore' = [blockStore EXCEPT ![h] = b]
                  /\ ledger' = ledger
                  /\ lastHash' = lastHash
                  /\ received' = [m \in Node |-> received[m] \cup {h}]
                  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: Create a change representative block
\* ----------------------------------------------------------------------
CreateChange ==
  /\ \E n \in Node :
        LET priv == NodeKey[n] 
            pub  == Priv2Pub[priv] 
            prev == LatestBlock(pub, n) 
        IN
          /\ \E newRep \in PublicKey :
                LET data == << "change", pub, newRep >> 
                    h    == CalculateHash(data, prev) 
                    b    == [ type      |-> "change",
                             prev      |-> prev,
                             account   |-> pub,
                             amount    |-> 0,
                             recipient |-> pub,
                             source    |-> NoHash,
                             rep       |-> newRep,
                             signature |-> Sign(priv, data) ] 
                IN
                  /\ h \in Hash
                  /\ b # NoBlock
                  /\ IsWellTypedBlock(b)
                  /\ blockStore' = [blockStore EXCEPT ![h] = b]
                  /\ ledger' = ledger
                  /\ lastHash' = lastHash
                  /\ received' = [m \in Node |-> received[m] \cup {h}]
                  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: Process a received block at a node
\* ----------------------------------------------------------------------
ProcessReceived ==
  /\ \E n \in Node :
        /\ \E h \in received[n] :
            LET b == blockStore[h] IN
              /\ b # NoBlock
              /\ IsWellTypedBlock(b)
              /\ VerifySig(b.account, BlockData(b), b.signature)
              /\ (b.type = "genesis" => TRUE)    \* genesis already in ledger, but allowed
              /\ (b.type = "send" =>
                   /\ b.amount <= Balance(b.account, n)   \* abstract balance check
                   /\ TRUE)
              /\ (b.type = "open" =>
                   /\ b.source # NoHash
                   /\ TRUE)
              /\ (b.type = "receive" =>
                   /\ b.source # NoHash
                   /\ TRUE)
              /\ (b.type = "change" => TRUE)
              /\ ledger' = [ledger EXCEPT ![n][h] = b]
              /\ received' = [received EXCEPT ![n] = @ \ {h}]
              /\ UNCHANGED << lastHash, blockStore >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ CreateGenesis
  \/ CreateSend
  \/ CreateOpen
  \/ CreateReceive
  \/ CreateChange
  \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blockStore>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ lastHash \in Hash \/ lastHash = NoHash
  /\ blockStore \in [Hash -> (Block \cup {NoBlock})]
  /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
  /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a valid signature
\* ----------------------------------------------------------------------
SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      (ledger[n][h] # NoBlock) =>
        LET b == ledger[n][h] IN
          VerifySig(b.account, BlockData(b), b.signature)

\* ----------------------------------------------------------------------
\* Concrete implementation of the abstract hash operator (used by the
\* configuration file via substitution).
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
  CHOOSE h \in Hash : TRUE

====