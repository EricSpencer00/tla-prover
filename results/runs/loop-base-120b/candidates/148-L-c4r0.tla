---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,                \* The set of all possible block hashes
    NoHashVal,           \* Sentinel value indicating the absence of a hash
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply of coins at genesis (a natural number)
    NoBlockVal,          \* Sentinel value indicating no block
    CalculateHash,       \* Abstract hash operator (substituted by CalculateHashImpl)
    NoHash,              \* Alias for NoHashVal (used in specifications)
    NoBlock              \* Alias for NoBlockVal (used in specifications)

\* Additional abstract constants required for signatures
CONSTANT Sig

\* Mapping from private keys to their corresponding public keys
CONSTANT PrivateToPublic \* : [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,            \* The hash of the most recently created block (or NoHashVal)
    ledger,              \* [Node -> [Hash -> Block]] : validated blocks per node
    received,            \* [Node -> SUBSET Hash]   : hashes pending validation per node
    blocks               \* [Hash -> Block]          : all created blocks (validated or not)

\* ----------------------------------------------------------------------
\* Block record definition
\* ----------------------------------------------------------------------
Block ==
    [ type       : {"genesis", "send", "open", "receive", "change"},
      prev       : Hash,
      account    : PublicKey,
      recipient  : PublicKey,
      amount     : Nat,
      signature  : Sig,
      data       : STRING ]

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives
\* ----------------------------------------------------------------------
Sign(priv, data) == 
    (* Returns a signature value for the given private key and data.
       The concrete implementation is supplied by the model checker. *)
    CHOOSE s \in Sig : TRUE

VerifySignature(pub, sig, data) ==
    (* Returns TRUE iff sig is a valid signature of data under pub. *)
    CHOOSE b \in BOOLEAN : TRUE

\* ----------------------------------------------------------------------
\* Hash calculation (abstract, will be substituted by CalculateHashImpl)
\* ----------------------------------------------------------------------
CalculateHash(prev, data) == 
    (* Abstract hash function; the .cfg file replaces it with CalculateHashImpl. *)
    NoHashVal

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsGenesisCreated == lastHash # NoHashVal

BlockValid(b) == 
    /\ b \in Block
    /\ VerifySignature(b.account, b.signature, b.data)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]
    /\ blocks = [h \in Hash |-> NoBlockVal]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* ---- 1. Create Genesis Block ----------------------------------------
CreateGenesis ==
    /\ ~IsGenesisCreated
    /\ \E priv \in PrivateKey :
          LET pub == PrivateToPublic[priv] IN
          LET data == "Genesis:" \o ToString(GenesisBalance) IN
          LET newHash == CalculateHash(NoHashVal, data) IN
          LET blk == [ type       |-> "genesis",
                       prev       |-> NoHashVal,
                       account    |-> pub,
                       recipient  |-> pub,
                       amount     |-> GenesisBalance,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ newHash # NoHashVal
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocks'   = [blocks EXCEPT ![newHash] = blk]
          /\ ledger'   = [n \in Node |-> [h \in Hash |-> IF h = newHash THEN blk ELSE ledger[n][h]]]
          /\ received' = received
          /\ UNCHANGED << >>

\* ---- 2. Create Send Block -------------------------------------------
CreateSend ==
    /\ IsGenesisCreated
    /\ \E sender \in Node, priv \in PrivateKey, recPub \in PublicKey, amt \in Nat :
          LET senderPub == PrivateToPublic[priv] IN
          LET data == "Send:" \o ToString(amt) \o ":" \o recPub IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "send",
                       prev       |-> lastHash,
                       account    |-> senderPub,
                       recipient  |-> recPub,
                       amount     |-> amt,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocks'   = [blocks EXCEPT ![newHash] = blk]
          /\ received' = [n \in Node |-> received[n] \cup {newHash}]
          /\ UNCHANGED << ledger >>

\* ---- 3. Create Open Block -------------------------------------------
CreateOpen ==
    /\ IsGenesisCreated
    /\ \E opener \in Node, priv \in PrivateKey, sendHash \in Hash :
          LET openerPub == PrivateToPublic[priv] IN
          LET data == "Open:" \o ToString(sendHash) IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "open",
                       prev       |-> NoHashVal,
                       account    |-> openerPub,
                       recipient  |-> openerPub,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocks'   = [blocks EXCEPT ![newHash] = blk]
          /\ received' = [n \in Node |-> received[n] \cup {newHash}]
          /\ UNCHANGED << ledger >>

\* ---- 4. Create Receive Block ----------------------------------------
CreateReceive ==
    /\ IsGenesisCreated
    /\ \E receiver \in Node, priv \in PrivateKey, sendHash \in Hash :
          LET receiverPub == PrivateToPublic[priv] IN
          LET data == "Receive:" \o ToString(sendHash) IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "receive",
                       prev       |-> lastHash,
                       account    |-> receiverPub,
                       recipient  |-> receiverPub,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocks'   = [blocks EXCEPT ![newHash] = blk]
          /\ received' = [n \in Node |-> received[n] \cup {newHash}]
          /\ UNCHANGED << ledger >>

\* ---- 5. Create Change Representative Block ---------------------------
CreateChangeRep ==
    /\ IsGenesisCreated
    /\ \E node \in Node, priv \in PrivateKey, newRep \in PublicKey :
          LET nodePub == PrivateToPublic[priv] IN
          LET data == "ChangeRep:" \o newRep IN
          LET newHash == CalculateHash(lastHash, data) IN
          LET blk == [ type       |-> "change",
                       prev       |-> lastHash,
                       account    |-> nodePub,
                       recipient  |-> newRep,
                       amount     |-> 0,
                       signature  |-> Sign(priv, data),
                       data       |-> data ] IN
          /\ BlockValid(blk)
          /\ lastHash' = newHash
          /\ blocks'   = [blocks EXCEPT ![newHash] = blk]
          /\ received' = [n \in Node |-> received[n] \cup {newHash}]
          /\ UNCHANGED << ledger >>

\* ---- 6. Process a received block ------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
          /\ received[n] # {}
          /\ \E h \in received[n] :
                LET blk == blocks[h] IN
                /\ blk # NoBlockVal
                /\ BlockValid(blk)
                /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
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
    \/ CreateChangeRep
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<lastHash, ledger, received, blocks>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> Block]]
    /\ received \in [Node -> SUBSET Hash]
    /\ blocks \in [Hash -> Block]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic validity)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            (ledger[n][h] # NoBlockVal) => 
                BlockValid(ledger[n][h])

\* ----------------------------------------------------------------------
\* Exported definitions required by the .cfg file
\* ----------------------------------------------------------------------
CalculateHashImpl(prev, data) ==
    (* A simple bounded hash implementation for finite model checking.
       It chooses a hash different from NoHashVal, if possible. *)
    CHOOSE h \in Hash : h # NoHashVal

====