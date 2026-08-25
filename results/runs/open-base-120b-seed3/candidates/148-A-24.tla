---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash,            \* The set of all possible block hashes
    NoHashVal,       \* Sentinel value for "no hash"
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total amount of coins created in the genesis block
    NoBlockVal,      \* Sentinel value for "no block"
    CalculateHash,   \* Abstract hash calculation operator (overridden by CalculateHashImpl)
    NoHash,          \* Alias for NoHashVal (sentinel hash)
    NoBlock          \* Alias for NoBlockVal (sentinel block)

\*--------------------------------------------------------------------
\* Aliases for the sentinel constants
NoHash == NoHashVal
NoBlock == NoBlockVal

\*--------------------------------------------------------------------
\* Definition of a block record (the fields that are relevant for all
\* block types).  Fields that are not used by a particular block type
\* may contain the sentinel values.
BlockRecord ==
    [ type        : {"genesis", "send", "open", "receive", "change"},
      prev        : Hash,
      account     : PublicKey,
      amount      : Nat,
      destination : PublicKey,
      signature   : STRING ]

\* The domain of values that can appear in a ledger entry
BlockOrNo == BlockRecord \cup { NoBlock }

\*--------------------------------------------------------------------
\* Variables
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* Mapping: Node -> (Hash -> BlockOrNo)
    received    \* Mapping: Node -> SUBSET Hash (blocks pending validation)

vars == << lastHash, ledger, received >>

\*--------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]

\*--------------------------------------------------------------------
\* Helper: broadcast a newly created block to every node
BroadcastBlock(b, h) ==
    /\ ledger' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n][h2] ] ]
    /\ received' = [ n \in Node |-> received[n] \cup { h } ]
    /\ UNCHANGED lastHash

\*--------------------------------------------------------------------
\* Action: create the genesis block (can happen only once)
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E pk \in PublicKey, sk \in PrivateKey :
        /\ (* ownership relation is abstracted away *)
        LET
            b  == [ type        |-> "genesis",
                    prev        |-> NoHash,
                    account     |-> pk,
                    amount      |-> GenesisBalance,
                    destination |-> NoHash,
                    signature   |-> "sig" ]
            h  == CalculateHash(b, NoHash)
        IN
        /\ h # NoHash
        /\ lastHash' = h
        /\ BroadcastBlock(b, h)
        /\ UNCHANGED <<>>

\*--------------------------------------------------------------------
\* Action: create a send block
CreateSend ==
    /\ lastHash # NoHash
    /\ \E senderNode \in Node,
          pk        \in PublicKey,
          sk        \in PrivateKey,
          dest      \in PublicKey,
          amt       \in Nat :
        /\ (* abstract ownership and balance check are omitted *)
        LET
            b == [ type        |-> "send",
                   prev        |-> lastHash,
                   account     |-> pk,
                   amount      |-> amt,
                   destination |-> dest,
                   signature   |-> "sig" ]
            h == CalculateHash(b, lastHash)
        IN
        /\ h # NoHash
        /\ lastHash' = h
        /\ BroadcastBlock(b, h)
        /\ UNCHANGED <<>>

\*--------------------------------------------------------------------
\* Action: create an open block (first block of a new account)
CreateOpen ==
    /\ lastHash # NoHash
    /\ \E openerNode \in Node,
          pk        \in PublicKey,
          sk        \in PrivateKey,
          srcHash   \in Hash :
        /\ (* srcHash is assumed to be a send block addressed to pk *)
        LET
            b == [ type        |-> "open",
                   prev        |-> NoHash,
                   account     |-> pk,
                   amount      |-> 0,
                   destination |-> NoHash,
                   signature   |-> "sig" ]
            h == CalculateHash(b, NoHash)
        IN
        /\ h # NoHash
        /\ lastHash' = h
        /\ BroadcastBlock(b, h)
        /\ UNCHANGED <<>>

\*--------------------------------------------------------------------
\* Action: create a receive block
CreateReceive ==
    /\ lastHash # NoHash
    /\ \E receiverNode \in Node,
          pk           \in PublicKey,
          sk           \in PrivateKey,
          srcHash      \in Hash :
        /\ (* srcHash is assumed to be an unclaimed send block to pk *)
        LET
            b == [ type        |-> "receive",
                   prev        |-> lastHash,
                   account     |-> pk,
                   amount      |-> 0,
                   destination |-> NoHash,
                   signature   |-> "sig" ]
            h == CalculateHash(b, lastHash)
        IN
        /\ h # NoHash
        /\ lastHash' = h
        /\ BroadcastBlock(b, h)
        /\ UNCHANGED <<>>

\*--------------------------------------------------------------------
\* Action: create a change representative block
CreateChange ==
    /\ lastHash # NoHash
    /\ \E node \in Node,
          pk   \in PublicKey,
          sk   \in PrivateKey,
          newRep \in PublicKey :
        LET
            b == [ type        |-> "change",
                   prev        |-> lastHash,
                   account     |-> pk,
                   amount      |-> 0,
                   destination |-> newRep,
                   signature   |-> "sig" ]
            h == CalculateHash(b, lastHash)
        IN
        /\ h # NoHash
        /\ lastHash' = h
        /\ BroadcastBlock(b, h)
        /\ UNCHANGED <<>>

\*--------------------------------------------------------------------
\* Action: a node processes a pending block (validation is abstracted)
ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
        /\ ledger[n][h] # NoBlock   \* the block has already been broadcast
        /\ (* abstract validation, assumed true *)
        /\ received' = [ received EXCEPT ![n] = @ \ { h } ]
        /\ UNCHANGED << lastHash, ledger >>

\*--------------------------------------------------------------------
\* The next-state relation
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\*--------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> BlockOrNo]]
    /\ received \in [Node -> SUBSET Hash]

\*--------------------------------------------------------------------
\* Placeholder for signature validation (always true in this abstract model)
SignatureValid(b) == TRUE

\* Cryptographic safety invariant: every stored block has a valid signature
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            /\ ledger[n][h] # NoBlock
            => SignatureValid(ledger[n][h])

\*--------------------------------------------------------------------
\* Concrete implementation of the abstract hash operator.
\* This definition will be overridden by the .cfg substitution
\* (CalculateHashImpl substituted for CalculateHash).
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : h # NoHash

\* Bind the abstract name to the concrete implementation
CalculateHash == CalculateHashImpl

=============================================================================