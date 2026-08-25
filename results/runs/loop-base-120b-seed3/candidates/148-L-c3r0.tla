---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,               \* Set of all possible block hashes
    NoHashVal,          \* Sentinel value meaning “no hash”
    PrivateKey,         \* Set of private keys
    PublicKey,          \* Set of public keys
    Node,               \* Set of network nodes
    GenesisBalance,    \* Total supply of coins (a natural number)
    NoBlockVal,         \* Sentinel value meaning “no block”
    CalculateHash,      \* Abstract hash operator (will be overridden)
    NoHash,             \* Alias for NoHashVal (sentinel hash)
    NoBlock,            \* Alias for NoBlockVal (sentinel block)
    PrivateToPublic,    \* Mapping PrivateKey -> PublicKey
    NodePrivKey,        \* Mapping Node -> PrivateKey
    Sig                 \* Set of possible signatures

\* ----------------------------------------------------------------------
\* Aliases for the sentinel values
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Record definition for a block
Block ==
    [ type      : {"genesis", "send", "receive", "open", "change"},
      prevHash  : Hash \cup {NoHash},
      account   : PublicKey,
      dest      : PublicKey,
      amount    : Nat,
      sig       : Sig ]

\* ----------------------------------------------------------------------
\* Abstract cryptographic primitives (treated as uninterpreted)
Sign(priv, data) == <<priv, data>>
Verify(pub, data, s) ==
    \E priv \in PrivateKey :
        /\ PrivateToPublic[priv] = pub
        /\ s = Sign(priv, data)

\* ----------------------------------------------------------------------
\* Abstract hash function (will be substituted by CalculateHashImpl)
CalculateHash(blk, prev) == CalculateHashImpl(blk, prev)

(*  The configuration file will replace CalculateHash with a concrete
    implementation named CalculateHashImpl.  For completeness we provide
    a trivial definition that picks an arbitrary hash from the set. *)
CalculateHashImpl(blk, prev) == CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    lastHash,    \* The hash of the most recently created block, or NoHash
    ledger,      \* Node -> (Hash -> Block \cup {NoBlock})
    received,    \* Node -> SUBSET Hash   (blocks waiting to be processed)
    blocks       \* Hash -> Block \cup {NoBlock}   (created but not yet stored)

vars == << lastHash, ledger, received, blocks >>

\* ----------------------------------------------------------------------
\* Helper function: balance of an account according to a particular ledger copy
Balance(acc, l) ==
    LET
        allHashes == { h \in Hash : l[h] # NoBlock },
        accBlocks  == { l[h] : h \in allHashes : l[h].account = acc }
    IN
        ( +/
            { b.amount : b \in accBlocks :
                b.type \in {"genesis", "receive", "open"} } )
      -
        ( +/
            { b.amount : b \in accBlocks :
                b.type = "send" } )

\* ----------------------------------------------------------------------
\* Validation of a block against a node's local ledger copy
Validate(blk, l) ==
    /\ Verify(blk.account, blk, blk.sig)
    /\ CASE blk.type = "genesis" -> TRUE
       [] blk.type = "send" ->
            /\ blk.prevHash # NoHash
            /\ l[blk.prevHash] # NoBlock
            /\ Balance(blk.account, l) >= blk.amount
       [] blk.type = "open" ->
            /\ blk.prevHash = NoHash
            /\ blk.dest = blk.account
            (* The referenced send block must exist and be unclaimed; abstracted *)
            /\ TRUE
       [] blk.type = "receive" ->
            /\ blk.prevHash # NoHash
            /\ l[blk.prevHash] # NoBlock
            (* The referenced send block must exist and be unclaimed; abstracted *)
            /\ TRUE
       [] blk.type = "change" ->
            /\ blk.prevHash # NoHash
            /\ l[blk.prevHash] # NoBlock
       [] OTHER -> FALSE

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlock ] ]
    /\ received = [ n \in Node |-> {} ]
    /\ blocks = [ h \in Hash |-> NoBlock ]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (once)
GenesisAction ==
    /\ lastHash = NoHash
    /\ \E n \in Node :
          LET priv == NodePrivKey[n]
              pub  == PrivateToPublic[priv]
              blk  == [ type      |-> "genesis",
                       prevHash  |-> NoHash,
                       account   |-> pub,
                       dest      |-> pub,
                       amount    |-> GenesisBalance,
                       sig       |-> Sign(priv, <<pub, GenesisBalance>> ) ]
              h    == CalculateHash(blk, NoHash)
          IN /\ h \in Hash
             /\ blocks'   = [blocks EXCEPT ![h] = blk]
             /\ lastHash' = h
             /\ received' = [ m \in Node |-> received[m] \cup {h} ]
             /\ UNCHANGED <<ledger>>

\* ----------------------------------------------------------------------
\* Action: create a send block
SendAction ==
    /\ lastHash # NoHash
    /\ \E n \in Node, dest \in PublicKey, amt \in Nat :
          LET priv == NodePrivKey[n]
              pub  == PrivateToPublic[priv]
              prev == 
                 (* choose the latest block of the sender in this node's ledger;
                    abstracted as any hash that belongs to the sender's chain *)
                 CHOOSE h \in Hash :
                    ledger[n][h] # NoBlock /\ ledger[n][h].account = pub
              blk  == [ type      |-> "send",
                       prevHash  |-> prev,
                       account   |-> pub,
                       dest      |-> dest,
                       amount    |-> amt,
                       sig       |-> Sign(priv, <<pub, dest, amt, prev>> ) ]
              h    == CalculateHash(blk, lastHash)
          IN /\ h \in Hash
             /\ Balance(pub, ledger[n]) >= amt
             /\ blocks'   = [blocks EXCEPT ![h] = blk]
             /\ lastHash' = h
             /\ received' = [ m \in Node |-> received[m] \cup {h} ]
             /\ UNCHANGED <<ledger>>

\* ----------------------------------------------------------------------
\* Action: create an open block (first block of a new account)
OpenAction ==
    /\ lastHash # NoHash
    /\ \E n \in Node, sendHash \in Hash :
          LET priv == NodePrivKey[n]
              pub  == PrivateToPublic[priv]
              sendBlk == blocks[sendHash]
          IN /\ sendBlk # NoBlock
             /\ sendBlk.type = "send"
             /\ sendBlk.dest = pub
             /\ blk == [ type      |-> "open",
                        prevHash  |-> NoHash,
                        account   |-> pub,
                        dest      |-> pub,
                        amount    |-> sendBlk.amount,
                        sig       |-> Sign(priv, <<pub, sendBlk.amount>> ) ]
             /\ h == CalculateHash(blk, lastHash)
             /\ h \in Hash
             /\ blocks'   = [blocks EXCEPT ![h] = blk]
             /\ lastHash' = h
             /\ received' = [ m \in Node |-> received[m] \cup {h} ]
             /\ UNCHANGED <<ledger>>

\* ----------------------------------------------------------------------
\* Action: create a receive block
ReceiveAction ==
    /\ lastHash # NoHash
    /\ \E n \in Node, sendHash \in Hash, prevHash \in Hash :
          LET priv == NodePrivKey[n]
              pub  == PrivateToPublic[priv]
              sendBlk == blocks[sendHash]
              prevBlk == ledger[n][prevHash]
          IN /\ sendBlk # NoBlock
             /\ sendBlk.type = "send"
             /\ sendBlk.dest = pub
             /\ prevBlk # NoBlock
             /\ prevBlk.account = pub
             /\ blk == [ type      |-> "receive",
                        prevHash  |-> prevHash,
                        account   |-> pub,
                        dest      |-> pub,
                        amount    |-> sendBlk.amount,
                        sig       |-> Sign(priv, <<pub, sendBlk.amount, prevHash>> ) ]
             /\ h == CalculateHash(blk, lastHash)
             /\ h \in Hash
             /\ blocks'   = [blocks EXCEPT ![h] = blk]
             /\ lastHash' = h
             /\ received' = [ m \in Node |-> received[m] \cup {h} ]
             /\ UNCHANGED <<ledger>>

\* ----------------------------------------------------------------------
\* Action: create a change representative block
ChangeAction ==
    /\ lastHash # NoHash
    /\ \E n \in Node, newRep \in PublicKey :
          LET priv == NodePrivKey[n]
              pub  == PrivateToPublic[priv]
              prev == 
                 CHOOSE h \in Hash :
                    ledger[n][h] # NoBlock /\ ledger[n][h].account = pub
              blk == [ type      |-> "change",
                       prevHash  |-> prev,
                       account   |-> pub,
                       dest      |-> newRep,
                       amount    |-> 0,
                       sig       |-> Sign(priv, <<pub, newRep, prev>> ) ]
              h == CalculateHash(blk, lastHash)
          IN /\ h \in Hash
             /\ blocks'   = [blocks EXCEPT ![h] = blk]
             /\ lastHash' = h
             /\ received' = [ m \in Node |-> received[m] \cup {h} ]
             /\ UNCHANGED <<ledger>>

\* ----------------------------------------------------------------------
\* Action: a node processes a received block
ProcessAction ==
    /\ \E n \in Node, h \in received[n] :
          LET blk == blocks[h]
          IN /\ blk # NoBlock
             /\ Validate(blk, ledger[n])
             /\ ledger'   = [ledger EXCEPT ![n][h] = blk]
             /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
             /\ UNCHANGED <<lastHash, blocks>>

\* ----------------------------------------------------------------------
Next ==
    \/ GenesisAction
    \/ SendAction
    \/ OpenAction
    \/ ReceiveAction
    \/ ChangeAction
    \/ ProcessAction

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ blocks \in [Hash -> Block \cup {NoBlock}]
    /\ \A n \in Node : ledger[n] \in [Hash -> Block \cup {NoBlock}]
    /\ \A n \in Node : received[n] \subseteq Hash

\* ----------------------------------------------------------------------
\* Safety invariant (all stored blocks have a valid signature)
SafetyInvariant ==
    /\ \A n \in Node :
          \A h \in Hash :
              LET blk == ledger[n][h] IN
              blk # NoBlock => Verify(blk.account, blk, blk.sig)

\* ----------------------------------------------------------------------
\* Public names required by the .cfg file
THEOREM SpecIsSpec == Spec
THEOREM TypeInv ==  []TypeInvariant
THEOREM SafetyInv == []SafetyInvariant

====