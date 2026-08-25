---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,                     \* the set of all possible block hashes
    NoHashVal,                \* sentinel value standing for “no hash”
    PrivateKey,               \* the set of all private keys
    PublicKey,                \* the set of all public keys
    Node,                     \* the set of network nodes
    GenesisBalance,           \* total supply of coins (a natural number)
    NoBlockVal,               \* sentinel value standing for “no block”
    CalculateHash,            \* abstract hash operator (will be overridden)
    NoHash,                   \* alias for NoHashVal
    NoBlock                   \* alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Aliases for the sentinel values
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Mappings that are assumed to be provided as constants
\* (they are not listed in the required identifiers, but they help the model)
PrivToPub \in [PrivateKey -> PublicKey]        \* private‑key → public‑key
NodeKey    \in [Node -> PrivateKey]            \* each node owns a private key

\* ----------------------------------------------------------------------
\* Definition of a block record.  Fields that are not used by a particular
\* block type may contain arbitrary values (they are ignored by the
\* validation predicates).
Block ==
    [ type    : {"Genesis","Send","Open","Receive","ChangeRep"},
      hash    : Hash,
      prev    : Hash,
      acct    : PublicKey,          \* owner of the account chain
      dest    : PublicKey,          \* destination account (Send)
      amount  : Nat,                \* amount transferred
      rep     : PublicKey,          \* new representative (ChangeRep)
      sigPriv : PrivateKey ]        \* private key that created the signature

\* ----------------------------------------------------------------------
\* The global state variables
VARIABLES
    LastHash,        \* the most recently calculated hash (global ordering)
    AllBlocks,       \* global pool of created blocks, indexed by hash
    Ledger,          \* per‑node copy of the distributed ledger
    Received         \* per‑node set of hashes that have been received but not yet processed

\* ----------------------------------------------------------------------
\* Helper predicates for block types
IsGenesis(b)   == b.type = "Genesis"
IsSend(b)      == b.type = "Send"
IsOpen(b)      == b.type = "Open"
IsReceive(b)   == b.type = "Receive"
IsChange(b)    == b.type = "ChangeRep"

\* ----------------------------------------------------------------------
\* Cryptographic checks (abstracted)
ValidSignature(b) ==
    /\ b.sigPriv \in PrivateKey
    /\ PrivToPub[b.sigPriv] = b.acct

\* ----------------------------------------------------------------------
\* Balance computation for an account in a given node's ledger
Amount(b) ==
    CASE
        b.type \in {"Genesis","Send","Open","Receive"} -> b.amount
        OTHER                                    -> 0

TotalReceived(ledger, acct) ==
    \* Sum of amounts in blocks that add funds to the account
    +\/ { h \in Hash :
            LET blk == ledger[h] IN
            blk # NoBlock /\ blk.acct = acct /\ blk.type \in {"Genesis","Open","Receive"} : Amount(blk) }

TotalSent(ledger, acct) ==
    \* Sum of amounts in send blocks originated from the account
    +\/ { h \in Hash :
            LET blk == ledger[h] IN
            blk # NoBlock /\ blk.acct = acct /\ blk.type = "Send" : Amount(blk) }

Balance(acct, ledger) ==
    TotalReceived(ledger, acct) - TotalSent(ledger, acct)

\* ----------------------------------------------------------------------
\* The abstract hash operator implementation that the .cfg file may
\* substitute for the constant CalculateHash.  It simply picks an
\* arbitrary hash from the set Hash.
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* The constant CalculateHash is assumed to be overridden by the
\* configuration file with CalculateHashImpl.  We provide a default
\* definition so the module type‑checks even without the override.
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* INITIAL STATE
Init ==
    /\ LastHash = NoHash
    /\ AllBlocks = [h \in Hash |-> NoBlock]
    /\ Ledger    = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received  = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* ACTION: create the genesis block (can happen only once)
CreateGenesis ==
    /\ LastHash = NoHash                         \* no block has been created yet
    /\ \* choose a node that will issue the genesis block
       n \in Node
    /\ let priv == NodeKey[n] in
       let pub  == PrivToPub[priv] in
    /\ let blk ==
          [ type    |-> "Genesis",
            hash    |-> newHash,
            prev    |-> NoHash,
            acct    |-> pub,
            dest    |-> NoHash,               \* unused
            amount  |-> GenesisBalance,
            rep     |-> NoHash,               \* unused
            sigPriv |-> priv ]
    /\ newHash == CalculateHash(blk, NoHash)
    /\ LastHash' = newHash
    /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = blk]
    /\ Ledger'    = [n' \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE Ledger[n'][h]]]
    /\ Received'  = [n' \in Node |-> Received[n']]   \* no pending blocks
    /\ UNCHANGED <<>> 

\* ----------------------------------------------------------------------
\* ACTION: create a send block by a node
CreateSend ==
    /\ LastHash # NoHash
    /\ n \in Node
    /\ let priv == NodeKey[n] in
       let pub  == PrivToPub[priv] in
    /\ let senderLedger == Ledger[n] in
    /\ Balance(pub, senderLedger) >= amount
    /\ amount \in Nat
    /\ destPub \in PublicKey
    /\ let blk ==
          [ type    |-> "Send",
            hash    |-> newHash,
            prev    |-> LastHash,
            acct    |-> pub,
            dest    |-> destPub,
            amount  |-> amount,
            rep     |-> NoHash,
            sigPriv |-> priv ]
    /\ newHash == CalculateHash(blk, LastHash)
    /\ LastHash' = newHash
    /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = blk]
    /\ Received'  = [n' \in Node |-> Received[n'] \cup {newHash}]
    /\ UNCHANGED <<Ledger>>

\* ----------------------------------------------------------------------
\* ACTION: create an open block (first block of a new account)
CreateOpen ==
    /\ n \in Node
    /\ let priv == NodeKey[n] in
       let pub  == PrivToPub[priv] in
    /\ \* there must exist a send block that targets this public key and has not yet been opened
       \E h \in Hash :
         LET sb == AllBlocks[h] IN
         sb # NoBlock /\ IsSend(sb) /\ sb.dest = pub /\ ~\E h2 \in Hash :
             LET ob == AllBlocks[h2] IN
             ob # NoBlock /\ IsOpen(ob) /\ ob.acct = pub
    /\ let blk ==
          [ type    |-> "Open",
            hash    |-> newHash,
            prev    |-> NoHash,
            acct    |-> pub,
            dest    |-> NoHash,
            amount  |-> 0,                \* amount is derived from the referenced send block
            rep     |-> NoHash,
            sigPriv |-> priv ]
    /\ newHash == CalculateHash(blk, NoHash)
    /\ LastHash' = newHash
    /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = blk]
    /\ Received'  = [n' \in Node |-> Received[n'] \cup {newHash}]
    /\ UNCHANGED <<Ledger>>

\* ----------------------------------------------------------------------
\* ACTION: create a receive block
CreateReceive ==
    /\ n \in Node
    /\ let priv == NodeKey[n] in
       let pub  == PrivToPub[priv] in
    /\ \* there must be a pending send block addressed to this account
       \E hSend \in Hash :
         LET sb == AllBlocks[hSend] IN
         sb # NoBlock /\ IsSend(sb) /\ sb.dest = pub /\
         ~\E hRecv \in Hash :
             LET rb == AllBlocks[hRecv] IN
             rb # NoBlock /\ IsReceive(rb) /\ rb.prev = hSend
    /\ let blk ==
          [ type    |-> "Receive",
            hash    |-> newHash,
            prev    |-> LastHash,
            acct    |-> pub,
            dest    |-> NoHash,
            amount  |-> 0,               \* amount is taken from the referenced send block
            rep     |-> NoHash,
            sigPriv |-> priv ]
    /\ newHash == CalculateHash(blk, LastHash)
    /\ LastHash' = newHash
    /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = blk]
    /\ Received'  = [n' \in Node |-> Received[n'] \cup {newHash}]
    /\ UNCHANGED <<Ledger>>

\* ----------------------------------------------------------------------
\* ACTION: create a change‑representative block
CreateChangeRep ==
    /\ n \in Node
    /\ let priv == NodeKey[n] in
       let pub  == PrivToPub[priv] in
    /\ newRep \in PublicKey
    /\ let blk ==
          [ type    |-> "ChangeRep",
            hash    |-> newHash,
            prev    |-> LastHash,
            acct    |-> pub,
            dest    |-> NoHash,
            amount  |-> 0,
            rep     |-> newRep,
            sigPriv |-> priv ]
    /\ newHash == CalculateHash(blk, LastHash)
    /\ LastHash' = newHash
    /\ AllBlocks' = [AllBlocks EXCEPT ![newHash] = blk]
    /\ Received'  = [n' \in Node |-> Received[n'] \cup {newHash}]
    /\ UNCHANGED <<Ledger>>

\* ----------------------------------------------------------------------
\* ACTION: a node processes a received block
ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in Received[node] :
         LET blk == AllBlocks[h] IN
         /\ blk # NoBlock
         /\ ValidSignature(blk)               \* cryptographic check
         /\ (* block‑type specific validation *)
            CASE
              blk.type = "Send"    -> 
                 (blk.amount <= Balance(blk.acct, Ledger[node]))
              blk.type = "Open"    -> 
                 (\E hs \in Hash :
                      LET sb == AllBlocks[hs] IN
                      sb # NoBlock /\ IsSend(sb) /\ sb.dest = blk.acct)
              blk.type = "Receive" -> 
                 (\E hs \in Hash :
                      LET sb == AllBlocks[hs] IN
                      sb # NoBlock /\ IsSend(sb) /\ sb.dest = blk.acct /\
                      ~\E hr \in Hash :
                         LET rb == AllBlocks[hr] IN
                         rb # NoBlock /\ IsReceive(rb) /\ rb.prev = hs)
              blk.type = "ChangeRep" -> TRUE
              blk.type = "Genesis" -> TRUE
         /\ Ledger' = [Ledger EXCEPT ![node][h] = blk]
         /\ Received' = [Received EXCEPT ![node] = @ \ {h}]
         /\ UNCHANGED <<LastHash, AllBlocks>>
    /\ TRUE

\* ----------------------------------------------------------------------
\* The overall NEXT relation
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChangeRep
    \/ \E n \in Node : ProcessBlock(n)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<LastHash, AllBlocks, Ledger, Received>>

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
TypeInvariant ==
    /\ LastHash \in Hash \/ {NoHash}
    /\ AllBlocks \in [Hash -> (Block \cup {NoBlock})]
    /\ Ledger \in [Node -> [Hash -> (Block \cup {NoBlock})]]
    /\ Received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* SAFETY INVARIANT (cryptographic)
SafetyInvariant ==
    \A n \in Node :
       \A h \in Hash :
          (Ledger[n][h] # NoBlock) => ValidSignature(Ledger[n][h])

\* ----------------------------------------------------------------------
\* The set of invariants that the configuration file will refer to
INVARIANTS == TypeInvariant /\ SafetyInvariant

====