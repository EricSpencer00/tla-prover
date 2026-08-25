---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* The set of all possible block hashes
    NoHashVal,     \* Sentinel hash value indicating "no hash"
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins at genesis
    NoBlockVal,    \* Sentinel value for an absent block
    CalculateHash, \* Abstract hash calculation operator (to be overridden)
    NoHash,        \* Alias for the sentinel hash
    NoBlock        \* Alias for the sentinel block

\* ----------------------------------------------------------------------
\* Aliases for the sentinel constants
NoHash   == NoHashVal
NoBlock  == NoBlockVal

\* ----------------------------------------------------------------------
\* Mapping from private keys to their corresponding public keys.
\* This is a constant function that must be provided in the .cfg file.
VARIABLES
    privToPub

\* Mapping from each node to the private key it owns.
VARIABLES
    ownedKey

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,            \* the most recent block hash (or NoHash)
    ledger,              \* mapping from hashes to blocks (or NoBlock)
    received             \* mapping from each node to the set of pending block hashes

\* ----------------------------------------------------------------------
\* Block record definition
Block == [
    type       : {"genesis", "send", "open", "receive", "change"},
    prev       : Hash,
    account    : PublicKey,
    destination: PublicKey,
    amount     : Nat,
    sig        : PrivateKey,
    hash       : Hash
]

\* ----------------------------------------------------------------------
\* Abstract hash calculation operator (will be substituted by CalculateHashImpl)
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* Default (placeholder) implementation of CalculateHash.
\* The real model checking configuration will replace this with a finite version.
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Helper: verify that a block's signature matches the public key of its account
SigOK(b) == privToPub[b.sig] = b.account

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> NoBlock]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can happen only once)
GenesisCreate ==
    /\ lastHash = NoHash
    /\ \E pk \in PublicKey :
          LET h  == CHOOSE hh \in Hash : hh # NoHash
              blk == [type        |-> "genesis",
                      prev        |-> NoHash,
                      account     |-> pk,
                      destination |-> pk,
                      amount      |-> GenesisBalance,
                      sig         |-> CHOOSE priv \in PrivateKey : privToPub[priv] = pk,
                      hash        |-> h]
          IN
              /\ ledger' = [ledger EXCEPT ![h] = blk]
              /\ lastHash' = h
              /\ UNCHANGED ownedKey
              /\ UNCHANGED privToPub
              /\ received' = [n \in Node |-> {h}]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a send block
SendCreate ==
    /\ \E n \in Node, priv \in PrivateKey :
          LET pub == privToPub[priv] IN
          LET prevHash == 
                ( \* find the latest hash for this account; for simplicity we pick any existing hash \*)
                CHOOSE h \in Hash : ledger[h] # NoBlock /\ ledger[h].account = pub
          IN
          LET amount == CHOOSE a \in Nat : a <= GenesisBalance
          LET h == CHOOSE hh \in Hash : hh # NoHash
          LET dest == CHOOSE pk \in PublicKey : pk # pub
          LET blk == [type        |-> "send",
                      prev        |-> prevHash,
                      account     |-> pub,
                      destination |-> dest,
                      amount      |-> amount,
                      sig         |-> priv,
                      hash        |-> h]
          IN
              /\ ledger' = [ledger EXCEPT ![h] = blk]
              /\ lastHash' = h
              /\ received' = [n' \in Node |-> IF n' = n THEN received[n'] \cup {h} ELSE received[n']]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create an open block (opening a new account)
OpenCreate ==
    /\ \E n \in Node, priv \in PrivateKey :
          LET pub == privToPub[priv] IN
          LET sendHash == CHOOSE sh \in Hash :
                ledger[sh] # NoBlock /\ ledger[sh].type = "send" /\ ledger[sh].destination = pub
          LET h == CHOOSE hh \in Hash : hh # NoHash
          LET blk == [type        |-> "open",
                      prev        |-> NoHash,
                      account     |-> pub,
                      destination |-> pub,
                      amount      |-> ledger[sendHash].amount,
                      sig         |-> priv,
                      hash        |-> h]
          IN
              /\ ledger' = [ledger EXCEPT ![h] = blk]
              /\ lastHash' = h
              /\ received' = [n' \in Node |-> IF n' = n THEN received[n'] \cup {h} ELSE received[n']]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a receive block
ReceiveCreate ==
    /\ \E n \in Node, priv \in PrivateKey :
          LET pub == privToPub[priv] IN
          LET prevHash == 
                CHOOSE h \in Hash : ledger[h] # NoBlock /\ ledger[h].account = pub
          LET sendHash == CHOOSE sh \in Hash :
                ledger[sh] # NoBlock /\ ledger[sh].type = "send" /\ ledger[sh].destination = pub
          LET h == CHOOSE hh \in Hash : hh # NoHash
          LET blk == [type        |-> "receive",
                      prev        |-> prevHash,
                      account     |-> pub,
                      destination |-> pub,
                      amount      |-> ledger[sendHash].amount,
                      sig         |-> priv,
                      hash        |-> h]
          IN
              /\ ledger' = [ledger EXCEPT ![h] = blk]
              /\ lastHash' = h
              /\ received' = [n' \in Node |-> IF n' = n THEN received[n'] \cup {h} ELSE received[n']]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a change representative block
ChangeRepCreate ==
    /\ \E n \in Node, priv \in PrivateKey :
          LET pub == privToPub[priv] IN
          LET prevHash == 
                CHOOSE h \in Hash : ledger[h] # NoBlock /\ ledger[h].account = pub
          LET newRep == CHOOSE pk \in PublicKey : pk # pub
          LET h == CHOOSE hh \in Hash : hh # NoHash
          LET blk == [type        |-> "change",
                      prev        |-> prevHash,
                      account     |-> pub,
                      destination |-> newRep,
                      amount      |-> 0,
                      sig         |-> priv,
                      hash        |-> h]
          IN
              /\ ledger' = [ledger EXCEPT ![h] = blk]
              /\ lastHash' = h
              /\ received' = [n' \in Node |-> IF n' = n THEN received[n'] \cup {h} ELSE received[n']]
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: process a received block at a node
ProcessReceived ==
    /\ \E n \in Node, h \in received[n] :
          LET blk == ledger[h] IN
          /\ blk # NoBlock
          /\ SigOK(blk)
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED << lastHash, ledger >>
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ GenesisCreate
    \/ SendCreate
    \/ OpenCreate
    \/ ReceiveCreate
    \/ ChangeRepCreate
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    /\ Init
    /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Hash -> (NoBlock \cup Block)]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Cryptographic safety invariant: every stored block has a matching signature
SafetyInvariant ==
    \A h \in Hash :
        LET blk == ledger[h] IN
        IF blk = NoBlock THEN TRUE
        ELSE privToPub[blk.sig] = blk.account

\* ----------------------------------------------------------------------
\* The set of properties to be checked (only invariants here)
PROPERTIES == TypeInvariant /\ SafetyInvariant

====