---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* CONSTANTS (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash,
    NoHash, NoBlock

\* ----------------------------------------------------------------------
\* Additional constants needed for the specification (may be left
\* uninterpreted by the model checker)
\* ----------------------------------------------------------------------
CONSTANTS PrivToPub \* mapping PrivateKey -> PublicKey

\* ----------------------------------------------------------------------
\* Block datatype
\* ----------------------------------------------------------------------
Block ==
    [ btype  : {"Genesis", "Send", "Open", "Receive", "Change"},
      prevH  : Hash,
      account: PublicKey,
      dest   : PublicKey,
      amount : Nat,
      sig    : PublicKey,
      hash   : Hash ]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,          \* the most recent block hash (global ordering)
    Ledger,            \* per‑node copy of the distributed ledger
    Received,          \* per‑node set of blocks received but not yet processed
    BalanceMap         \* current balance of each public key

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << LastHash, Ledger, Received, BalanceMap >>

\* CalculateHashImpl is the concrete implementation that the .cfg file
\* substitutes for the abstract constant CalculateHash.
CalculateHashImpl(data, prev) ==
    CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger   = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
    /\ Received = [ n \in Node |-> {} ]
    /\ BalanceMap = [ pk \in PublicKey |-> 0 ]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (only once)
\* ----------------------------------------------------------------------
Genesis ==
    /\ LastHash = NoHash
    /\ \E sk \in PrivateKey :
          LET pk == PrivToPub[sk] IN
          LET h  == CalculateHash(
                     [ btype   |-> "Genesis",
                       prevH   |-> NoHash,
                       account |-> pk,
                       dest    |-> NoHash,
                       amount  |-> GenesisBalance,
                       sig     |-> pk,
                       hash    |-> NoHash ],
                     NoHash) IN
          LET blk == [ btype   |-> "Genesis",
                       prevH   |-> NoHash,
                       account |-> pk,
                       dest    |-> NoHash,
                       amount  |-> GenesisBalance,
                       sig     |-> pk,
                       hash    |-> h ] IN
            /\ LastHash' = h
            /\ Ledger'   = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledger[n][h2] ] ]
            /\ Received' = [ n \in Node |-> {} ]
            /\ BalanceMap' = [ pk2 \in PublicKey |-> IF pk2 = pk THEN GenesisBalance ELSE 0 ]

\* ----------------------------------------------------------------------
\* Action: create a send block
\* ----------------------------------------------------------------------
CreateSend ==
    /\ LastHash # NoHash
    /\ \E sk \in PrivateKey, dest \in PublicKey, amt \in Nat :
          LET pk == PrivToPub[sk] IN
            /\ amt <= BalanceMap[pk]
            /\ LET h == CalculateHash(
                     [ btype   |-> "Send",
                       prevH   |-> LastHash,
                       account |-> pk,
                       dest    |-> dest,
                       amount  |-> amt,
                       sig     |-> pk,
                       hash    |-> NoHash ],
                     LastHash) IN
               LET blk == [ btype   |-> "Send",
                            prevH   |-> LastHash,
                            account |-> pk,
                            dest    |-> dest,
                            amount  |-> amt,
                            sig     |-> pk,
                            hash    |-> h ] IN
                 /\ LastHash' = h
                 /\ Ledger' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledger[n][h2] ] ]
                 /\ Received' = [ n \in Node |-> Received[n] \cup {blk} ]
                 /\ BalanceMap' = [ pk2 \in PublicKey |-> IF pk2 = pk THEN BalanceMap[pk2] - amt ELSE BalanceMap[pk2] ]

\* ----------------------------------------------------------------------
\* Action: create an open block (opens a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ LastHash # NoHash
    /\ \E sk \in PrivateKey, sendBlk \in Block :
          LET pk == PrivToPub[sk] IN
            /\ sendBlk.btype = "Send"
            /\ sendBlk.dest = pk
            /\ LET h == CalculateHash(
                     [ btype   |-> "Open",
                       prevH   |-> NoHash,
                       account |-> pk,
                       dest    |-> NoHash,
                       amount  |-> sendBlk.amount,
                       sig     |-> pk,
                       hash    |-> NoHash ],
                     NoHash) IN
               LET blk == [ btype   |-> "Open",
                            prevH   |-> NoHash,
                            account |-> pk,
                            dest    |-> NoHash,
                            amount  |-> sendBlk.amount,
                            sig     |-> pk,
                            hash    |-> h ] IN
                 /\ LastHash' = h
                 /\ Ledger' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledger[n][h2] ] ]
                 /\ Received' = [ n \in Node |-> Received[n] \cup {blk} ]
                 /\ BalanceMap' = [ pk2 \in PublicKey |-> IF pk2 = pk THEN sendBlk.amount ELSE BalanceMap[pk2] ]

\* ----------------------------------------------------------------------
\* Action: create a receive block
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ LastHash # NoHash
    /\ \E sk \in PrivateKey, sendBlk \in Block, prevHash \in Hash :
          LET pk == PrivToPub[sk] IN
            /\ sendBlk.btype = "Send"
            /\ sendBlk.dest = pk
            /\ LET h == CalculateHash(
                     [ btype   |-> "Receive",
                       prevH   |-> prevHash,
                       account |-> pk,
                       dest    |-> NoHash,
                       amount  |-> sendBlk.amount,
                       sig     |-> pk,
                       hash    |-> NoHash ],
                     prevHash) IN
               LET blk == [ btype   |-> "Receive",
                            prevH   |-> prevHash,
                            account |-> pk,
                            dest    |-> NoHash,
                            amount  |-> sendBlk.amount,
                            sig     |-> pk,
                            hash    |-> h ] IN
                 /\ LastHash' = h
                 /\ Ledger' = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledger[n][h2] ] ]
                 /\ Received' = [ n \in Node |-> Received[n] \cup {blk} ]
                 /\ BalanceMap' = [ pk2 \in PublicKey |-> IF pk2 = pk THEN BalanceMap[pk2] + sendBlk.amount ELSE BalanceMap[pk2] ]

\* ----------------------------------------------------------------------
\* Action: create a change representative block
\* ----------------------------------------------------------------------
CreateChange ==
    /\ LastHash # NoHash
    /\ \E sk \in PrivateKey, newRep \in PublicKey :
          LET pk == PrivToPub[sk] IN
          LET h == CalculateHash(
                     [ btype   |-> "Change",
                       prevH   |-> LastHash,
                       account |-> pk,
                       dest    |-> newRep,
                       amount  |-> 0,
                       sig     |-> pk,
                       hash    |-> NoHash ],
                     LastHash) IN
          LET blk == [ btype   |-> "Change",
                       prevH   |-> LastHash,
                       account |-> pk,
                       dest    |-> newRep,
                       amount  |-> 0,
                       sig     |-> pk,
                       hash    |-> h ] IN
            /\ LastHash' = h
            /\ Ledger'   = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN blk ELSE Ledger[n][h2] ] ]
            /\ Received' = [ n \in Node |-> Received[n] \cup {blk} ]
            /\ UNCHANGED BalanceMap

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ Genesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash
    /\ Ledger   \in [Node -> [Hash -> (NoBlockVal \cup Block)]]
    /\ Received \in [Node -> SUBSET Block]
    /\ BalanceMap \in [PublicKey -> Nat]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic signature validity)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    /\ \A n \in Node : \A h \in Hash :
          LET b == Ledger[n][h] IN
          IF b = NoBlockVal
          THEN TRUE
          ELSE b.sig = b.account

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====