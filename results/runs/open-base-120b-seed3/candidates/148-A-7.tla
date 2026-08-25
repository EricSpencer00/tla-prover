---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

(*************************************************************************)
(*  CONSTANTS (to be instantiated in the .cfg file)                     *)
(*************************************************************************)
CONSTANTS
    Hash,               \* Universe of block hash values
    NoHashVal,          \* Sentinel value meaning “no hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value meaning “no block”
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Alias for the sentinel hash value
    NoBlock             \* Alias for the sentinel block value

(*************************************************************************)
(*  Additional constants required for the abstract model                 *)
(*************************************************************************)
CONSTANTS
    PrivToPub,          \* Mapping from a private key to its public key
    NodeToPriv          \* Mapping from a node to the private key it owns

(*************************************************************************)
(*  Types of blocks                                                      *)
(*************************************************************************)
Block == 
    [ type      : {"genesis","send","receive","open","change"},
      prev      : Hash \/ {NoHash},
      account   : PublicKey,
      recipient : PublicKey \/ {NoHash},
      amount    : Nat,
      signature : STRING ]

\* A block can also be the sentinel NoBlockVal
BlockOrEmpty == Block \/ {NoBlockVal}

(*************************************************************************)
(*  STATE VARIABLES                                                      *)
(*************************************************************************)
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* Mapping from hash values to blocks (or NoBlockVal)
    received    \* Mapping from each node to the set of hashes it has received but not yet processed

(*************************************************************************)
(*  Helper definitions                                                   *)
(*************************************************************************)
\* Compute the balance of an account by traversing its chain.
Balance(pub, l) ==
    LET chain == [h \in Hash |-> IF l[h] # NoBlockVal /\ l[h].account = pub THEN h ELSE NoHash] IN
    BalanceFromChain(pub, chain, l)

BalanceFromChain(pub, chain, l) ==
    IF chain = {} THEN 0
    ELSE
        LET h == CHOOSE hh \in chain : TRUE IN
        CASE l[h].type = "genesis" -> l[h].amount,
             l[h].type = "receive" -> BalanceFromChain(pub, chain \ {h}, l) + l[h].amount,
             l[h].type = "send"    -> BalanceFromChain(pub, chain \ {h}, l) - l[h].amount,
             OTHER                -> BalanceFromChain(pub, chain \ {h}, l)

\* Abstract signature verification (treated as always true for this model)
ValidSignature(b) ==
    TRUE

\* Abstract hash calculation (will be overridden by CalculateHashImpl)
CalculateHashImpl(b, prev) ==
    CHOOSE h \in Hash : TRUE

\* For readability, define the set of all possible block hashes (including the sentinel)
AllHashes == Hash \/ {NoHash}

(*************************************************************************)
(*  INITIAL STATE                                                        *)
(*************************************************************************)
Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

(*************************************************************************)
(*  ACTIONS                                                               *)
(*************************************************************************)

\*--- Genesis block creation----------------------------------------------
GenesisBlock ==
    /\ lastHash = NoHash
    /\ \E pk \in PublicKey :
          \* Assume the owner of the genesis private key creates the block
          LET priv == CHOOSE p \in PrivateKey : PrivToPub[p] = pk IN
          LET b == [ type      |-> "genesis",
                     prev      |-> NoHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> GenesisBalance,
                     signature |-> "sig" ] IN
          LET h == CalculateHashImpl(b, NoHash) IN
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = b]
          /\ received' = [n \in Node |-> received[n] \cup {h}]
          /\ UNCHANGED << >>   \* no other variables

\*--- Send block creation--------------------------------------------------
SendBlock ==
    /\ \E n \in Node :
          LET priv == NodeToPriv[n] IN
          LET pk   == PrivToPub[priv] IN
          \* Find the hash of the latest block in this account's chain
          LET prevHash == 
                IF lastHash = NoHash THEN NoHash
                ELSE
                  CHOOSE h \in Hash :
                       ledger[h] # NoBlockVal /\ ledger[h].account = pk /\ ledger[h].prev = lastHash
          /\ \E amt \in Nat :
               amt <= Balance(pk, ledger)
               /\ LET b == [ type      |-> "send",
                             prev      |-> prevHash,
                             account   |-> pk,
                             recipient |-> CHOOSE r \in PublicKey : r # pk,
                             amount    |-> amt,
                             signature |-> "sig"] IN
               LET h == CalculateHashImpl(b, prevHash) IN
               /\ h \in Hash
               /\ lastHash' = h
               /\ ledger' = [ledger EXCEPT ![h] = b]
               /\ received' = [m \in Node |-> received[m] \cup {h}]
               /\ UNCHANGED << >>  

\*--- Open block creation--------------------------------------------------
OpenBlock ==
    /\ \E n \in Node :
          LET priv == NodeToPriv[n] IN
          LET pk   == PrivToPub[priv] IN
          \* A send block that targets this public key must exist
          /\ \E sendHash \in Hash :
                ledger[sendHash] # NoBlockVal /\
                ledger[sendHash].type = "send" /\
                ledger[sendHash].recipient = pk /\
                ledger[sendHash].prev # NoHash   \* ensure it is not the genesis block
          LET b == [ type      |-> "open",
                     prev      |-> NoHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> ledger[sendHash].amount,
                     signature |-> "sig"] IN
          LET h == CalculateHashImpl(b, NoHash) IN
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = b]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

\*--- Receive block creation-----------------------------------------------
ReceiveBlock ==
    /\ \E n \in Node :
          LET priv == NodeToPriv[n] IN
          LET pk   == PrivToPub[priv] IN
          \* Find a pending send block addressed to this account
          /\ \E sendHash \in Hash :
                ledger[sendHash] # NoBlockVal /\
                ledger[sendHash].type = "send" /\
                ledger[sendHash].recipient = pk /\
                \* Ensure this send has not yet been received
                ~(\E h \in Hash :
                      ledger[h] # NoBlockVal /\
                      ledger[h].type = "receive" /\
                      ledger[h].prev = sendHash)
          \* Find the previous block in this account's chain (if any)
          LET prevHash == 
                IF lastHash = NoHash THEN NoHash
                ELSE
                  CHOOSE h \in Hash :
                       ledger[h] # NoBlockVal /\ ledger[h].account = pk /\ ledger[h].prev = lastHash
          LET b == [ type      |-> "receive",
                     prev      |-> prevHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> ledger[sendHash].amount,
                     signature |-> "sig"] IN
          LET h == CalculateHashImpl(b, prevHash) IN
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = b]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

\*--- Change representative block creation---------------------------------
ChangeRepBlock ==
    /\ \E n \in Node :
          LET priv == NodeToPriv[n] IN
          LET pk   == PrivToPub[priv] IN
          LET prevHash == 
                IF lastHash = NoHash THEN NoHash
                ELSE
                  CHOOSE h \in Hash :
                       ledger[h] # NoBlockVal /\ ledger[h].account = pk /\ ledger[h].prev = lastHash
          LET b == [ type      |-> "change",
                     prev      |-> prevHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> 0,
                     signature |-> "sig"] IN
          LET h == CalculateHashImpl(b, prevHash) IN
          /\ h \in Hash
          /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![h] = b]
          /\ received' = [m \in Node |-> received[m] \cup {h}]
          /\ UNCHANGED << >>

\*--- Process a received block on a node ---------------------------------
ProcessBlock ==
    /\ \E n \in Node :
          /\ received[n] # {}
          /\ \E h \in received[n] :
                ledger[h] # NoBlockVal /\                \* block is known in the global ledger
                ValidSignature(ledger[h]) /\             \* signature checks out
                (\* reference checks, simplified *\
                 IF ledger[h].type = "send" THEN
                    ledger[h].prev # NoHash
                 ELSE IF ledger[h].type = "receive" THEN
                    ledger[h].prev # NoHash
                 ELSE TRUE) /\
                received' = [m \in Node |-> 
                              IF m = n THEN received[m] \ {h}
                              ELSE received[m]]
                /\ UNCHANGED << lastHash, ledger >>

\*--- The overall Next relation -------------------------------------------
Next ==
    \/ GenesisBlock
    \/ SendBlock
    \/ OpenBlock
    \/ ReceiveBlock
    \/ ChangeRepBlock
    \/ ProcessBlock

(*************************************************************************)
(*  SPECIFICATION                                                        *)
(*************************************************************************)
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

(*************************************************************************)
(*  INVARIANTS                                                            *)
(*************************************************************************)
TypeInvariant ==
    /\ lastHash \in Hash \/ {NoHash}
    /\ ledger \in [Hash -> BlockOrEmpty]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    /\ \A h \in Hash :
          ledger[h] # NoBlockVal => ValidSignature(ledger[h])

(*************************************************************************)
(*  Operator to be substituted in by the .cfg file                         *)
(*************************************************************************)
CalculateHashImpl(b, prev) ==
    CHOOSE h \in Hash : TRUE

====