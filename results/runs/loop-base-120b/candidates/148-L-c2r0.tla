---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,           \* the set of possible block hashes
    NoHashVal,      \* sentinel hash value meaning "no hash"
    PrivateKey,     \* set of private keys
    PublicKey,      \* set of public keys
    Node,           \* set of network nodes
    GenesisBalance, \* total supply of coins (a natural number)
    NoBlockVal,     \* sentinel value meaning "no block"
    CalculateHash,  \* abstract hash operator (overridden by CalculateHashImpl)
    NoHash,         \* synonym for NoHashVal
    NoBlock         \* synonym for NoBlockVal

\* ----------------------------------------------------------------------
\* Mappings between private and public keys (assumed to be a bijection)
ASSUME
    \* PrivToPub maps each private key to its public key
    \E PrivToPub \in [PrivateKey -> PublicKey] :
        TRUE

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,   \* the most recent block hash (global)
    ledger,     \* per‑node copy of the distributed ledger: Node -> (Hash -> Block)
    received,   \* per‑node set of hashes awaiting validation: Node -> SUBSET Hash
    blockPool   \* global mapping from hash to the block data (including pending blocks)

\* ----------------------------------------------------------------------
\* Types and sentinel values
NoHash == NoHashVal
NoBlock == NoBlockVal

Block ==
    [ type      : {"genesis", "send", "open", "receive", "change"},
      signer    : PrivateKey,
      account   : PublicKey,
      prevHash  : Hash,
      data      : Seq(Nat),          \* placeholder for amounts, recipients, etc.
      signature : PrivateKey ]

IsBlock(b) == b # NoBlock

IsValidBlock(b) ==
    /\ b.type \in {"genesis","send","open","receive","change"}
    /\ b.signer \in PrivateKey
    /\ b.account \in PublicKey
    /\ b.prevHash \in Hash
    /\ b.signature \in PrivateKey

ValidSignature(b) ==
    /\ IsValidBlock(b)
    /\ PrivToPub[b.signer] = b.account

IsValidLedgerEntry(e) ==
    (e = NoBlock) \/ IsValidBlock(e)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ blockPool = [h \in Hash |-> NoBlock]

\* ----------------------------------------------------------------------
\* Helper operator to compute a new hash (abstract)
CalculateHashImpl(b, prev) ==
    CHOOSE h \in Hash : TRUE

\* By default CalculateHash is just an alias; the .cfg file will replace it
CalculateHash(b, prev) == CalculateHashImpl(b, prev)

\* ----------------------------------------------------------------------
\* Actions

\*--- Genesis block creation (can occur only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E signer \in PrivateKey :
          LET blk ==
                [ type      |-> "genesis",
                  signer    |-> signer,
                  account   |-> PrivToPub[signer],
                  prevHash  |-> NoHash,
                  data      |-> <<GenesisBalance>>,
                  signature |-> signer ]
          IN
          /\ ValidSignature(blk)
          /\ newHash == CalculateHash(blk, NoHash)
          /\ lastHash' = newHash
          /\ blockPool' = [blockPool EXCEPT ![newHash] = blk]
          /\ received' = [n \in Node |-> {newHash}]
          /\ ledger'   = [n \in Node |-> [ledger[n] EXCEPT ![newHash] = blk]]
          /\ UNCHANGED <<>>   \* no other variables change

\*--- Create a send block (reduces sender balance, designates a recipient)
CreateSend ==
    /\ \E n \in Node :
        \E signer \in PrivateKey :
            /\ PrivToPub[signer] = senderAcc
            /\ senderAcc \in PublicKey
            /\ \E amount \in Nat :
                \E recipient \in PublicKey :
                    LET blk ==
                        [ type      |-> "send",
                          signer    |-> signer,
                          account   |-> senderAcc,
                          prevHash  |-> lastHash,
                          data      |-> <<amount, recipient>>,
                          signature |-> signer ]
                    IN
                    /\ ValidSignature(blk)
                    /\ newHash == CalculateHash(blk, lastHash)
                    /\ lastHash' = newHash
                    /\ blockPool' = [blockPool EXCEPT ![newHash] = blk]
                    /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                    /\ UNCHANGED <<ledger, received>>

\*--- Create an open block (first block of a new account)
CreateOpen ==
    /\ \E n \in Node :
        \E signer \in PrivateKey :
            /\ PrivToPub[signer] = newAcc
            /\ newAcc \in PublicKey
            /\ \E sendHash \in Hash :
                /\ blockPool[sendHash] # NoBlock
                /\ blockPool[sendHash].type = "send"
                /\ blockPool[sendHash].data[2] = newAcc   \* recipient matches the new account
                LET blk ==
                    [ type      |-> "open",
                      signer    |-> signer,
                      account   |-> newAcc,
                      prevHash  |-> NoHash,
                      data      |-> <<sendHash>>,
                      signature |-> signer ]
                IN
                /\ ValidSignature(blk)
                /\ newHash == CalculateHash(blk, NoHash)
                /\ lastHash' = newHash
                /\ blockPool' = [blockPool EXCEPT ![newHash] = blk]
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED <<ledger, received>>

\*--- Create a receive block (claims a previously sent amount)
CreateReceive ==
    /\ \E n \in Node :
        \E signer \in PrivateKey :
            /\ PrivToPub[signer] = recvAcc
            /\ recvAcc \in PublicKey
            /\ \E sendHash \in Hash :
                /\ blockPool[sendHash] # NoBlock
                /\ blockPool[sendHash].type = "send"
                /\ blockPool[sendHash].data[2] = recvAcc
                LET blk ==
                    [ type      |-> "receive",
                      signer    |-> signer,
                      account   |-> recvAcc,
                      prevHash  |-> lastHash,
                      data      |-> <<sendHash>>,
                      signature |-> signer ]
                IN
                /\ ValidSignature(blk)
                /\ newHash == CalculateHash(blk, lastHash)
                /\ lastHash' = newHash
                /\ blockPool' = [blockPool EXCEPT ![newHash] = blk]
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED <<ledger, received>>

\*--- Change representative block
CreateChange ==
    /\ \E n \in Node :
        \E signer \in PrivateKey :
            /\ PrivToPub[signer] = acc
            /\ \E newRep \in PublicKey :
                LET blk ==
                    [ type      |-> "change",
                      signer    |-> signer,
                      account   |-> acc,
                      prevHash  |-> lastHash,
                      data      |-> <<newRep>>,
                      signature |-> signer ]
                IN
                /\ ValidSignature(blk)
                /\ newHash == CalculateHash(blk, lastHash)
                /\ lastHash' = newHash
                /\ blockPool' = [blockPool EXCEPT ![newHash] = blk]
                /\ received' = [m \in Node |-> received[m] \cup {newHash}]
                /\ UNCHANGED <<ledger, received>>

\*--- Process (validate) a received block at a node
ProcessBlock ==
    /\ \E n \in Node :
        /\ \E h \in received[n] :
            LET blk == blockPool[h] IN
            /\ blk # NoBlock
            /\ ValidSignature(blk)
            /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
            /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
            /\ UNCHANGED <<lastHash, blockPool>>

\*--- Overall next-state relation
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\*--- Specification
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blockPool>>

\*--- Type invariant
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ blockPool \in [Hash -> Block]
    /\ \A n \in Node: \A h \in Hash: IsValidLedgerEntry(ledger[n][h])
    /\ \A h \in Hash: IsValidLedgerEntry(blockPool[h])

\*--- Safety invariant (all blocks stored in ledgers have valid signatures)
SafetyInvariant ==
    /\ \A n \in Node: \A h \in Hash:
          ledger[n][h] # NoBlock => ValidSignature(ledger[n][h])

====