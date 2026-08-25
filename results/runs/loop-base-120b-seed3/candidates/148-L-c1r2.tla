---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,               \* set of all possible block hashes
    NoHashVal,          \* sentinel value for “no hash”
    PrivateKey,         \* set of private keys
    PublicKey,          \* set of public keys
    Node,               \* set of network nodes
    GenesisBalance,    \* total supply created by the genesis block
    NoBlockVal,         \* sentinel value for “no block”
    CalculateHash,      \* abstract hash operator (will be overridden)
    NoHash,             \* alias for NoHashVal (sentinel)
    NoBlock             \* alias for NoBlockVal (sentinel)

\* ----------------------------------------------------------------------
\* Aliases for the sentinel values
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Mapping from a private key to its corresponding public key
\* (provided as a constant; the configuration may instantiate it)
CONSTANT PrivateToPublic \* : [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Definition of a block.  All fields are present; some are ignored
\* depending on the block type.
Block ==
    [ type      : {"genesis", "send", "open", "receive", "change"},
      account   : PublicKey,               \* owner of the account chain
      prev      : Hash \cup {NoHash},      \* hash of previous block in the chain
      dest      : PublicKey \cup {NoHash},\* destination account (send/open)
      source    : Hash \cup {NoHash},      \* referenced send block (receive/open)
      rep       : PublicKey \cup {NoHash},\* representative (change)
      amount    : Nat,                     \* amount transferred (send/receive)
      signature : PrivateKey               \* private key that signed the block
    ]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    LastHash,          \* the most recent block hash (or NoHash)
    Ledger,            \* mapping from each hash to a Block or NoBlock
    Received           \* mapping from each node to the set of pending hashes

vars == << LastHash, Ledger, Received >>

\* ----------------------------------------------------------------------
\* Helper abstractions (left uninterpreted for model checking)

\* The hash of a block is computed from the block data and the previous hash.
CalculateHashImpl(data, prev) == CHOOSE h : FALSE
\* The configuration will substitute CalculateHashImpl for CalculateHash.

CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* Abstract function returning the current balance of an account.
Balance(acc) == CHOOSE b : FALSE

\* Returns the hash of the latest block on the chain of a given account,
\* or NoHash if the account has no blocks yet.
LatestHash(acc) == CHOOSE h : FALSE

\* Checks whether a block’s signature matches the public key that owns its chain.
ValidSignature(blk) ==
    PrivateToPublic[blk.signature] = blk.account

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [ h \in Hash |-> NoBlock ]
    /\ Received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can happen only once)
GenesisCreate ==
    /\ LastHash = NoHash
    /\ \E priv \in PrivateKey :
          LET pub == PrivateToPublic[priv],
              blk == [ type      |-> "genesis",
                       account   |-> pub,
                       prev      |-> NoHash,
                       dest      |-> pub,
                       source    |-> NoHash,
                       rep       |-> NoHash,
                       amount    |-> GenesisBalance,
                       signature |-> priv ],
              h == CalculateHash(blk, LastHash)
          IN
              /\ LastHash' = h
              /\ Ledger' = [Ledger EXCEPT ![h] = blk]
              /\ Received' = [ n \in Node |-> Received[n] \cup {h} ]
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a send block
SendCreate ==
    /\ LastHash # NoHash
    /\ \E priv \in PrivateKey, dest \in PublicKey, amt \in Nat :
          LET pub == PrivateToPublic[priv],
              prevHash == LatestHash(pub),
              blk == [ type      |-> "send",
                       account   |-> pub,
                       prev      |-> prevHash,
                       dest      |-> dest,
                       source    |-> NoHash,
                       rep       |-> NoHash,
                       amount    |-> amt,
                       signature |-> priv ],
              h == CalculateHash(blk, LastHash)
          IN
              /\ prevHash # NoHash
              /\ amt <= Balance(pub)
              /\ dest # pub
              /\ LastHash' = h
              /\ Ledger' = [Ledger EXCEPT ![h] = blk]
              /\ Received' = [ n \in Node |-> Received[n] \cup {h} ]
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create an open block (first block of a new account)
OpenCreate ==
    /\ LastHash # NoHash
    /\ \E priv \in PrivateKey, srcHash \in Hash :
          LET pub == PrivateToPublic[priv],
              srcBlk == Ledger[srcHash],
              blk == [ type      |-> "open",
                       account   |-> pub,
                       prev      |-> NoHash,
                       dest      |-> pub,
                       source    |-> srcHash,
                       rep       |-> NoHash,
                       amount    |-> srcBlk.amount,
                       signature |-> priv ],
              h == CalculateHash(blk, LastHash)
          IN
              /\ srcBlk # NoBlock
              /\ srcBlk.type = "send"
              /\ srcBlk.dest = pub
              /\ LastHash' = h
              /\ Ledger' = [Ledger EXCEPT ![h] = blk]
              /\ Received' = [ n \in Node |-> Received[n] \cup {h} ]
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a receive block
ReceiveCreate ==
    /\ LastHash # NoHash
    /\ \E priv \in PrivateKey, srcHash \in Hash :
          LET pub == PrivateToPublic[priv],
              prevHash == LatestHash(pub),
              srcBlk == Ledger[srcHash],
              blk == [ type      |-> "receive",
                       account   |-> pub,
                       prev      |-> prevHash,
                       dest      |-> pub,
                       source    |-> srcHash,
                       rep       |-> NoHash,
                       amount    |-> srcBlk.amount,
                       signature |-> priv ],
              h == CalculateHash(blk, LastHash)
          IN
              /\ prevHash # NoHash
              /\ srcBlk # NoBlock
              /\ srcBlk.type = "send"
              /\ srcBlk.dest = pub
              /\ LastHash' = h
              /\ Ledger' = [Ledger EXCEPT ![h] = blk]
              /\ Received' = [ n \in Node |-> Received[n] \cup {h} ]
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a change representative block
ChangeCreate ==
    /\ LastHash # NoHash
    /\ \E priv \in PrivateKey, newRep \in PublicKey :
          LET pub == PrivateToPublic[priv],
              prevHash == LatestHash(pub),
              blk == [ type      |-> "change",
                       account   |-> pub,
                       prev      |-> prevHash,
                       dest      |-> pub,
                       source    |-> NoHash,
                       rep       |-> newRep,
                       amount    |-> 0,
                       signature |-> priv ],
              h == CalculateHash(blk, LastHash)
          IN
              /\ LastHash' = h
              /\ Ledger' = [Ledger EXCEPT ![h] = blk]
              /\ Received' = [ n \in Node |-> Received[n] \cup {h} ]
              /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node processes (validates) a pending block
ProcessNode ==
    /\ \E n \in Node, h \in Received[n] :
          LET blk == Ledger[h] IN
              /\ blk # NoBlock
              /\ ValidSignature(blk)
              \* Additional validation (referenced hashes exist, balance rules, etc.)
              /\ Received' = [Received EXCEPT ![n] = Received[n] \ {h}]
              /\ UNCHANGED << LastHash, Ledger >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeCreate
    \/ ProcessNode

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ Ledger \in [Hash -> (Block \/ {NoBlock})]
    /\ Received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a valid signature
SafetyInvariant ==
    \A h \in Hash :
        IF Ledger[h] # NoBlock
        THEN ValidSignature(Ledger[h])
        ELSE TRUE
====