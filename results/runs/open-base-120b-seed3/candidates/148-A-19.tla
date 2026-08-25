---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,               \* Set of all possible hash values
    NoHashVal,          \* A distinguished value used as a sentinel for hashes
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total amount of coins created at genesis (Nat)
    NoBlockVal,         \* Sentinel value for an empty block
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Sentinel hash representing “no previous hash”
    NoBlock             \* Sentinel block (unused, kept for compatibility)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block ==
    [ type       : {"genesis", "send", "open", "receive", "change"},
      account    : PublicKey,
      prev       : Hash \cup {NoHash},
      amount     : Nat,
      dest       : PublicKey \cup {NoBlock},
      sig        : STRING ]   \* abstract representation of a signature

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,       \* the most recent block hash (or NoHash)
    ledger,         \* per‑node ledger: Node -> (Hash -> Block)
    received,       \* per‑node set of hashes that have been received but not yet processed
    blockStore      \* global store of all created blocks: Hash -> Block

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* Mapping from a private key to its public key (abstract)
PubKeyOfPriv \in [PrivateKey -> PublicKey]

\* Mapping from a node to the private key it owns (abstract)
NodePrivKey \in [Node -> PrivateKey]

\* The public key that belongs to a node
PubKeyOfNode(n) == PubKeyOfPriv[NodePrivKey[n]]

\* Abstract balance function: walks the account chain and sums amounts
Balance(pk, l) == 
    LET
        chain == { h \in Hash : 
                     (\E b \in l[Node] : b = l[Node][h] /\ b.account = pk) }
    IN
        (* In a full spec this would walk the chain; here we abstract it *)
        CHOOSE b \in Nat : TRUE

\* Checks that a block’s signature is valid (abstract)
ValidSignature(b) == TRUE

\* Type‑specific validation (abstract – only stubbed for safety invariant)
ValidateBlock(b, n, l) ==
    /\ b.type = "send" => b.amount <= Balance(b.account, l)
    /\ b.type = "open" => b.prev = NoHash
    /\ b.type = "receive" => TRUE
    /\ b.type = "change" => TRUE
    /\ b.type = "genesis" => TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ blockStore = [h \in Hash |-> NoBlockVal]
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: Create genesis block (only once)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
        LET pk == PubKeyOfNode[n] IN
        LET b ==
            [ type    |-> "genesis",
              account |-> pk,
              prev    |-> NoHash,
              amount  |-> GenesisBalance,
              dest    |-> NoBlock,
              sig     |-> "sig" ]
        IN
        LET newHash == CalculateHash(b, NoHash) IN
        /\ newHash \in Hash
        /\ lastHash' = newHash
        /\ blockStore' = [blockStore EXCEPT ![newHash] = b]
        /\ ledger' = [n' \in Node |-> 
                        [h \in Hash |-> IF h = newHash THEN b ELSE ledger[n'][h]]]
        /\ received' = received
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Create a send block
\* ----------------------------------------------------------------------
CreateSend ==
    /\ lastHash # NoHash
    /\ \E n \in Node, amt \in Nat, dstPk \in PublicKey :
        LET pk == PubKeyOfNode[n] IN
        /\ amt <= Balance(pk, ledger)          \* abstract balance check
        LET b ==
            [ type    |-> "send",
              account |-> pk,
              prev    |-> lastHash,
              amount  |-> amt,
              dest    |-> dstPk,
              sig     |-> "sig" ]
        IN
        LET newHash == CalculateHash(b, lastHash) IN
        /\ newHash \in Hash
        /\ lastHash' = newHash
        /\ blockStore' = [blockStore EXCEPT ![newHash] = b]
        /\ ledger' = ledger
        /\ received' = [r \in Node |-> received[r] \cup {newHash}]
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Create an open block (opens a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ lastHash # NoHash
    /\ \E n \in Node, srcHash \in Hash :
        LET pk == PubKeyOfNode[n] IN
        LET srcBlock == blockStore[srcHash] IN
        /\ srcBlock.type = "send"
        /\ srcBlock.dest = pk
        LET b ==
            [ type    |-> "open",
              account |-> pk,
              prev    |-> NoHash,
              amount  |-> srcBlock.amount,
              dest    |-> NoBlock,
              sig     |-> "sig" ]
        IN
        LET newHash == CalculateHash(b, NoHash) IN
        /\ newHash \in Hash
        /\ lastHash' = newHash
        /\ blockStore' = [blockStore EXCEPT ![newHash] = b]
        /\ ledger' = ledger
        /\ received' = [r \in Node |-> received[r] \cup {newHash}]
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Create a receive block
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ lastHash # NoHash
    /\ \E n \in Node, sendHash \in Hash :
        LET pk == PubKeyOfNode[n] IN
        LET sendBlock == blockStore[sendHash] IN
        /\ sendBlock.type = "send"
        /\ sendBlock.dest = pk
        LET b ==
            [ type    |-> "receive",
              account |-> pk,
              prev    |-> lastHash,
              amount  |-> sendBlock.amount,
              dest    |-> sendHash,
              sig     |-> "sig" ]
        IN
        LET newHash == CalculateHash(b, lastHash) IN
        /\ newHash \in Hash
        /\ lastHash' = newHash
        /\ blockStore' = [blockStore EXCEPT ![newHash] = b]
        /\ ledger' = ledger
        /\ received' = [r \in Node |-> received[r] \cup {newHash}]
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Create a change‑representative block
\* ----------------------------------------------------------------------
CreateChange ==
    /\ lastHash # NoHash
    /\ \E n \in Node, newRep \in PublicKey :
        LET pk == PubKeyOfNode[n] IN
        LET b ==
            [ type    |-> "change",
              account |-> pk,
              prev    |-> lastHash,
              amount  |-> 0,
              dest    |-> newRep,
              sig     |-> "sig" ]
        IN
        LET newHash == CalculateHash(b, lastHash) IN
        /\ newHash \in Hash
        /\ lastHash' = newHash
        /\ blockStore' = [blockStore EXCEPT ![newHash] = b]
        /\ ledger' = ledger
        /\ received' = [r \in Node |-> received[r] \cup {newHash}]
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: Process a received block on a node
\* ----------------------------------------------------------------------
Process ==
    /\ \E n \in Node, h \in received[n] :
        LET b == blockStore[h] IN
        /\ b # NoBlockVal
        /\ ValidSignature(b)
        /\ ValidateBlock(b, n, ledger)
        /\ ledger' = [ledger EXCEPT ![n][h] = b]
        /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
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
    \/ Process

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blockStore>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ blockStore \in [Hash -> (Block \cup {NoBlockVal})]
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic correctness)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        IF ledger[n][h] # NoBlockVal
        THEN /\ ValidSignature(ledger[n][h])
             /\ ledger[n][h].account \in PublicKey
        ELSE TRUE

\* ----------------------------------------------------------------------
\* Implementation of CalculateHash (finite version for model checking)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* ASSUME the abstract operators are well‑typed
\* ----------------------------------------------------------------------
ASSUME
    /\ PubKeyOfPriv \in [PrivateKey -> PublicKey]
    /\ NodePrivKey \in [Node -> PrivateKey]

====