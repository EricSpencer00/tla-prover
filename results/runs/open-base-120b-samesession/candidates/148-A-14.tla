---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* Set of all possible hash values
    NoHashVal,     \* Sentinel hash value indicating "no hash"
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins at genesis (a natural number)
    NoBlockVal,    \* Sentinel value representing the absence of a block
    CalculateHash, \* Abstract hash calculation operator (overridden in .cfg)
    NoHash,        \* Alias for NoHashVal used in the model
    NoBlock        \* Alias for NoBlockVal used in the model

\* ----------------------------------------------------------------------
\* Aliases for the sentinel constants
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Mapping from private keys to their corresponding public keys (assumed bijective)
VARIABLES
    PrivToPub      \* Function: PrivateKey -> PublicKey

\* ----------------------------------------------------------------------
\* Block definition (record)
BLOCK == [
    type          : {"genesis","send","open","receive","change"},
    account       : PublicKey,
    previous      : Hash,
    amount        : Nat,
    recipient     : PublicKey \cup {NoHash},
    representative: PublicKey \cup {NoHash},
    signature     : PrivateKey
]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    LastHash,          \* The most recent block hash (or NoHash)
    Ledger,            \* [Node -> [Hash -> (BLOCK \cup {NoBlock})]]
    Received,          \* [Node -> SUBSET Hash]   (blocks pending validation)
    GenesisCreated     \* BOOLEAN flag ensuring genesis occurs once

\* ----------------------------------------------------------------------
\* Helper: a deterministic (but abstract) hash function used for model checking.
\* The .cfg file will substitute CalculateHash with CalculateHashImpl.
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Helper: amount contributed to balance by a block
Amount(b) ==
    CASE b.type = "genesis" -> b.amount
         [] b.type = "send"    -> -b.amount
         [] b.type = "receive"->  b.amount
         [] OTHER              -> 0

\* ----------------------------------------------------------------------
\* Helper: sum of a non‑empty set of natural numbers
Sum(S) ==
    IF S = {} THEN 0
    ELSE
        LET x == CHOOSE e \in S : TRUE IN
        x + Sum(S \ {x})

\* ----------------------------------------------------------------------
\* Balance of an account on a given node's ledger
Balance(node, acct, ledger) ==
    LET hashes == { h \in Hash :
                     ledger[h] # NoBlock /\ ledger[h].account = acct } IN
    Sum({ Amount(ledger[h]) : h \in hashes })

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]
    /\ GenesisCreated = FALSE
    /\ PrivToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (once)
CreateGenesis ==
    /\ ~GenesisCreated
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          /\ pub \in PublicKey
          /\ let blk == [type |-> "genesis",
                         account |-> pub,
                         previous |-> NoHash,
                         amount |-> GenesisBalance,
                         recipient |-> NoHash,
                         representative |-> NoHash,
                         signature |-> priv] in
          /\ newHash == CalculateHashImpl(blk, NoHash)
          /\ LastHash' = newHash
          /\ Ledger' = [n \in Node |
                         [h \in Hash |
                            IF h = newHash THEN blk ELSE Ledger[n][h]]]
          /\ Received' = [n \in Node |-> {}]
          /\ GenesisCreated' = TRUE
          /\ UNCHANGED <<PrivToPub>>
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: create a send block
CreateSend ==
    /\ GenesisCreated
    /\ \E n \in Node, priv \in PrivateKey :
          LET acct == PrivToPub[priv] IN
          /\ acct \in PublicKey
          /\ \E prev \in Hash :
                /\ Ledger[n][prev] # NoBlock
                /\ Ledger[n][prev].account = acct
                /\ LET bal == Balance(n, acct, Ledger[n]) IN
                   \E amt \in Nat :
                       /\ amt <= bal
                       /\ \E rec \in PublicKey :
                           LET blk == [type |-> "send",
                                      account |-> acct,
                                      previous |-> prev,
                                      amount |-> amt,
                                      recipient |-> rec,
                                      representative |-> NoHash,
                                      signature |-> priv] IN
                           /\ newHash == CalculateHashImpl(blk, prev)
                           /\ LastHash' = newHash
                           /\ Ledger' = [node \in Node |
                                          [h \in Hash |
                                             IF h = newHash THEN blk ELSE Ledger[node][h]]]
                           /\ Received' = [node \in Node |
                                            Received[node] \cup {newHash}]
                           /\ UNCHANGED <<GenesisCreated, PrivToPub>>
\* ----------------------------------------------------------------------
\* Action: create an open block (opens a new account using a received send)
CreateOpen ==
    /\ GenesisCreated
    /\ \E n \in Node, priv \in PrivateKey, sendHash \in Hash :
          LET acct == PrivToPub[priv] IN
          /\ acct \in PublicKey
          /\ /\ Ledger[n][sendHash] # NoBlock
             /\ Ledger[n][sendHash].type = "send"
             /\ Ledger[n][sendHash].recipient = acct
          /\ let blk == [type |-> "open",
                         account |-> acct,
                         previous |-> NoHash,
                         amount |-> Ledger[n][sendHash].amount,
                         recipient |-> NoHash,
                         representative |-> NoHash,
                         signature |-> priv] in
          /\ newHash == CalculateHashImpl(blk, NoHash)
          /\ LastHash' = newHash
          /\ Ledger' = [node \in Node |
                         [h \in Hash |
                            IF h = newHash THEN blk ELSE Ledger[node][h]]]
          /\ Received' = [node \in Node |
                           Received[node] \cup {newHash}]
          /\ UNCHANGED <<GenesisCreated, PrivToPub>>

\* ----------------------------------------------------------------------
\* Action: create a receive block (claims a previously sent amount)
CreateReceive ==
    /\ GenesisCreated
    /\ \E n \in Node, priv \in PrivateKey, sendHash \in Hash, prevHash \in Hash :
          LET acct == PrivToPub[priv] IN
          /\ acct \in PublicKey
          /\ /\ Ledger[n][sendHash] # NoBlock
             /\ Ledger[n][sendHash].type = "send"
             /\ Ledger[n][sendHash].recipient = acct
          /\ /\ Ledger[n][prevHash] # NoBlock
             /\ Ledger[n][prevHash].account = acct
          /\ let blk == [type |-> "receive",
                         account |-> acct,
                         previous |-> prevHash,
                         amount |-> Ledger[n][sendHash].amount,
                         recipient |-> NoHash,
                         representative |-> NoHash,
                         signature |-> priv] in
          /\ newHash == CalculateHashImpl(blk, prevHash)
          /\ LastHash' = newHash
          /\ Ledger' = [node \in Node |
                         [h \in Hash |
                            IF h = newHash THEN blk ELSE Ledger[node][h]]]
          /\ Received' = [node \in Node |
                           Received[node] \cup {newHash}]
          /\ UNCHANGED <<GenesisCreated, PrivToPub>>

\* ----------------------------------------------------------------------
\* Action: create a change representative block
CreateChange ==
    /\ GenesisCreated
    /\ \E n \in Node, priv \in PrivateKey, prev \in Hash, newRep \in PublicKey :
          LET acct == PrivToPub[priv] IN
          /\ acct \in PublicKey
          /\ /\ Ledger[n][prev] # NoBlock
             /\ Ledger[n][prev].account = acct
          /\ let blk == [type |-> "change",
                         account |-> acct,
                         previous |-> prev,
                         amount |-> 0,
                         recipient |-> NoHash,
                         representative |-> newRep,
                         signature |-> priv] in
          /\ newHash == CalculateHashImpl(blk, prev)
          /\ LastHash' = newHash
          /\ Ledger' = [node \in Node |
                         [h \in Hash |
                            IF h = newHash THEN blk ELSE Ledger[node][h]]]
          /\ Received' = [node \in Node |
                           Received[node] \cup {newHash}]
          /\ UNCHANGED <<GenesisCreated, PrivToPub>>

\* ----------------------------------------------------------------------
\* Action: process (validate) a received block at a node
ProcessBlock ==
    /\ \E n \in Node, h \in Received[n] :
          LET blk == Ledger[n][h] IN
          /\ blk # NoBlock
          /\ /\ blk.signature \in PrivateKey
             /\ PrivToPub[blk.signature] = blk.account
          /\ /\ blk.previous = NoHash \/ Ledger[n][blk.previous] # NoBlock
          /\ /\ CASE blk.type = "send"   -> 
                  Balance(n, blk.account, Ledger[n]) >= blk.amount
                [] blk.type = "open"   -> TRUE
                [] blk.type = "receive"->
                  \E sendH \in Hash :
                      Ledger[n][sendH] # NoBlock /\
                      Ledger[n][sendH].type = "send" /\
                      Ledger[n][sendH].recipient = blk.account /\
                      Ledger[n][sendH].amount = blk.amount
                [] OTHER -> TRUE
          /\ Received' = [node \in Node |
                           IF node = n THEN Received[node] \ {h}
                           ELSE Received[node]]
          /\ UNCHANGED <<LastHash, Ledger, GenesisCreated, PrivToPub>>

\* ----------------------------------------------------------------------
\* Next-state relation (any one of the actions may occur)
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, GenesisCreated>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger \in [Node -> [Hash -> (BLOCK \cup {NoBlock})]]
    /\ Received \in [Node -> SUBSET Hash]
    /\ GenesisCreated \in BOOLEAN
    /\ PrivToPub \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a signature that matches its account's public key
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET blk == Ledger[n][h] IN
            blk # NoBlock =>
                /\ blk.signature \in PrivateKey
                /\ PrivToPub[blk.signature] = blk.account

\* ----------------------------------------------------------------------
\* Exported identifiers
THEOREM SpecImpliesTypeInvariant == Spec => []TypeInvariant
THEOREM SpecImpliesSafetyInvariant == Spec => []SafetyInvariant

====