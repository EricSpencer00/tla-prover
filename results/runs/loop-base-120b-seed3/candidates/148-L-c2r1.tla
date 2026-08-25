---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,           \* Finite set of hash values
    NoHashVal,      \* Sentinel hash value
    PrivateKey,     \* Set of private keys
    PublicKey,      \* Set of public keys
    Node,           \* Set of network nodes
    GenesisBalance, \* Total supply of the cryptocurrency
    NoBlockVal,     \* Sentinel block value
    CalculateHash,  \* Abstract hash operator (will be overridden)
    NoHash,         \* Alias for NoHashVal
    NoBlock,        \* Alias for NoBlockVal
    PrivToPub,      \* Mapping from private keys to public keys
    NodePrivKey     \* Mapping from nodes to their owned private key

\* ----------------------------------------------------------------------
\* Helper aliases for the sentinels
\* ----------------------------------------------------------------------
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Assumptions about constant functions
\* ----------------------------------------------------------------------
ASSUME
    /\ PrivToPub \in [PrivateKey -> PublicKey]
    /\ NodePrivKey \in [Node -> PrivateKey]

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Block ==
    [ type            : {"genesis","send","open","receive","change"},
      prev            : Hash,
      account         : PublicKey,
      amount          : Nat,
      recipient       : PublicKey,
      representative  : PublicKey,
      signature       : Nat ]

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives
\* ----------------------------------------------------------------------
\* Simple abstract signing function (returns a dummy Nat)
Sign(priv, data) == 0

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* the hash of the most recently created block (or NoHash)
    ledger,     \* [Node -> [Hash -> Block]]  – each node's copy of the ledger
    received,   \* [Node -> SUBSET Hash]     – blocks waiting to be processed
    blocks      \* [Hash -> Block]           – globally known blocks

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ blocks = [h \in Hash |-> NoBlock]

\* ----------------------------------------------------------------------
\* Utility functions
\* ----------------------------------------------------------------------
\* Extract the data that is signed (all fields except the signature)
BlockData(b) ==
    << b.type, b.prev, b.account, b.amount, b.recipient, b.representative >>

\* Verify that a block's signature matches the public key of its account
ValidSignature(b) ==
    LET pk == b.account IN
    \E sk \in PrivateKey :
        /\ PrivToPub[sk] = pk
        /\ b.signature = Sign(sk, BlockData(b))

\* Compute the balance of a public key in a given ledger copy
Balance(pub, l) ==
    ( +/ { b.amount :
            h \in Hash,
            LET b == l[h] IN b # NoBlock /\ (b.type = "receive" \/ b.type = "open")
                /\ b.account = pub } )
    -
    ( +/ { b.amount :
            h \in Hash,
            LET b == l[h] IN b # NoBlock /\ b.type = "send"
                /\ b.account = pub } )

\* Choose an arbitrary public key (used for the genesis account)
GenesisPub == CHOOSE pk \in PublicKey : TRUE
GenesisPriv == CHOOSE sk \in PrivateKey : PrivToPub[sk] = GenesisPub

\* ----------------------------------------------------------------------
\* Block creation actions
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ LET h == CalculateHashImpl(<< "genesis", GenesisBalance >>, NoHash) IN
          h \in Hash
    /\ LET gBlock ==
            [ type            |-> "genesis",
              prev            |-> NoHash,
              account         |-> GenesisPub,
              amount          |-> GenesisBalance,
              recipient       |-> GenesisPub,          \* placeholder PubKey
              representative  |-> GenesisPub,          \* placeholder PubKey
              signature       |-> Sign(GenesisPriv, << "genesis", GenesisBalance >>) ] IN
    /\ blocks' = [blocks EXCEPT ![h] = gBlock]
    /\ lastHash' = h
    /\ ledger' = [n \in Node |-> [hash \in Hash |-> IF hash = h THEN gBlock ELSE NoBlock]]
    /\ received' = [n \in Node |-> {}]
    /\ UNCHANGED << >>

CreateSend ==
    /\ \E n \in Node :
          LET priv == NodePrivKey[n] IN
          LET pub  == PrivToPub[priv] IN
          LET bal  == Balance(pub, ledger[n]) IN
          \E amt \in Nat :
              amt <= bal
              /\ \E prevHash \in Hash :
                    blocks[prevHash] # NoBlock /\ blocks[prevHash].account = pub
                    /\ \E recPub \in PublicKey :
                          recPub # pub
                          /\ LET h == CalculateHashImpl(<< "send", prevHash, pub, amt, recPub >>, lastHash) IN
                               h \in Hash
                               /\ LET sBlock ==
                                      [ type            |-> "send",
                                        prev            |-> prevHash,
                                        account         |-> pub,
                                        amount          |-> amt,
                                        recipient       |-> recPub,
                                        representative  |-> GenesisPub,      \* placeholder PubKey
                                        signature       |-> Sign(priv, << "send", prevHash, pub, amt, recPub >>) ] IN
                                 /\ blocks' = [blocks EXCEPT ![h] = sBlock]
                                 /\ lastHash' = h
                                 /\ received' = [m \in Node |-> received[m] \cup {h}]
                                 /\ UNCHANGED ledger
                                 /\ TRUE

CreateOpen == FALSE   \* Placeholder – not modeled in this simplified spec
CreateReceive == FALSE
CreateChange == FALSE

\* ----------------------------------------------------------------------
\* Block processing action
\* ----------------------------------------------------------------------
ValidateBlock(node, b) ==
    /\ b.account \in PublicKey
    /\ (b.prev = NoHash) \/ (blocks[b.prev] # NoBlock)
    /\ ValidSignature(b)
    /\ CASE b.type = "send"   -> 
            LET pub == b.account IN
            b.amount <= Balance(pub, ledger[node])
       [] b.type = "open"   -> TRUE
       [] b.type = "receive"-> TRUE
       [] b.type = "change" -> TRUE
       [] b.type = "genesis"-> TRUE
       [] OTHER            -> FALSE

Process ==
    /\ \E n \in Node, h \in received[n] :
          LET b == blocks[h] IN
          /\ b # NoBlock
          /\ ValidateBlock(n, b)
          /\ ledger' = [ledger EXCEPT ![n][h] = b]
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED << lastHash, blocks >>

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
Spec == Init /\ [][Next]_<<lastHash, ledger, received, blocks>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ blocks \in [Hash -> Block]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic invariant)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    /\ \A n \in Node :
          \A h \in Hash :
              LET b == ledger[n][h] IN
              (b # NoBlock) => ValidSignature(b)

\* ----------------------------------------------------------------------
\* Abstract hash calculation implementation used for model checking
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

=============================================================================