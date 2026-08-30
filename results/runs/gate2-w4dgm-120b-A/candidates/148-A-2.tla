---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
          NoBlockVal, CalculateHash, NoHash, NoBlock

\* Hashes are an opaque domain; CalculateHash is treated as an uninterpreted
\* operator so the model is not tied to a concrete hash function.

\* Blocks are ordered by chain position rather than by hash order.
\* A block is valid only when its signature matches the public key of the
\* account that owns the chain the block sits on.

\* Finite Model Checking of block-lattice history is only ever
\* exploratory: the per-node ledger copies explode combinatorially
\* with every ordering of Create*/Process* actions, so a check on a tiny
\* hash set is not a proof of security for a real blockchain. It is
\* nonetheless a concrete sanity check against the invariants below.

ASSUME NoHashVal \notin Hash
ASSUME NoHash \notin Hash
ASSUME NoBlockVal \notin PrivateKey
ASSUME NoBlock \notin PrivateKey

OwnedBy == [n \in Node |-> {NodeToPublicKey[n]}]

\* Distributed ledger replicated across all nodes; each node's copy has
\* the same shape and the same contents as all the others.
Ledger == [n \in Node |-> [h \in Hash |-> NoBlockVal]]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

ZeroBalance == 0

\* A chain is the set of blocks an account's public key appears in; the
\* block itself carries the account's key, so the two agree.
Chain(pub) == {h \in Hash : ledger[CHOOSE n \in Node : TRUE][h] # NoBlockVal
                          /\ ledger[CHOOSE n \in Node : TRUE][h].account = pub}

BalanceAt(h) ==
  IF h = NoHash THEN 0
  ELSE LET b == ledger[CHOOSE n \in Node : TRUE][h] IN
       IF b.type = "send" THEN BalanceAt(b.prev) - b.amount
       ELSE IF b.type = "receive" THEN BalanceAt(b.prev) + b.amount
       ELSE BalanceAt(b.prev)

RECURSIVE Balance(_)
Balance(S) ==
  IF S = {} THEN 0
  ELSE LET pub == CHOOSE p \in S : TRUE IN BalanceAt(ChooseHash(pub))

AllChainsBalanced == Balance(PublicKey) = GenesisBalance

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> PrivateKey \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is the only block standing anywhere without a
\* predecessor; it sets the starting balance for the whole network.
CreateGenesisBlock ==
  /\ \E k \in PrivateKey, n \in Node :
       /\ NoHashVal \notin {ledger[CHOOSE m \in Node : TRUE][h] : h \in Hash}
       /\ \A h \in Hash : ledger[CHOOSE m \in Node : TRUE][h] = NoBlockVal
       /\ ledger' = [ledger EXCEPT ![n][NoHash] =
            [account |-> NodeToPublicKey[n], prev |-> NoHash,
             amount |-> GenesisBalance, type |-> "genesis", signer |-> k]]
  /\ lastHash' = NoHash
  /\ received' = [n \in Node |-> {NoHash}]

CreateSendBlock ==
  \E k \in PrivateKey, n \in Node, rcpt \in PublicKey, amt \in 1..GenesisBalance :
    LET pub == NodeToPublicKey[n] IN
    \E hPrev \in Chain(pub) :
      /\ BalanceAt(hPrev) >= amt
      /\ lastHash \notin Chain(pub)
      /\ LET h == CalculateHash([account |-> pub, prev |-> hPrev,
                                 amount |-> amt, type |-> "send", signer |-> k])
           IN /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] =
                   [account |-> pub, prev |-> hPrev, amount |-> amt,
                    type |-> "send", signer |-> k]]
              /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateOpenBlock ==
  \E k \in PrivateKey, n \in Node, snd \in Hash :
    LET pub == NodeToPublicKey[n] IN
    /\ ledger[CHOOSE m \in Node : TRUE][snd] # NoBlockVal
    /\ ledger[CHOOSE m \in Node : TRUE][snd].type = "send"
    /\ ledger[CHOOSE m \in Node : TRUE][snd].account = pub
    /\ lastHash \notin Chain(pub)
    /\ LET h == CalculateHash([account |-> pub, prev |-> snd,
                               amount |-> 0, type |-> "open", signer |-> k])
         IN /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] =
                 [account |-> pub, prev |-> snd, amount |-> 0,
                  type |-> "open", signer |-> k]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateReceiveBlock ==
  \E k \in PrivateKey, n \in Node, snd \in Hash :
    LET pub == NodeToPublicKey[n] IN
    /\ ledger[CHOOSE m \in Node : TRUE][snd] # NoBlockVal
    /\ ledger[CHOOSE m \in Node : TRUE][snd].type = "send"
    /\ ledger[CHOOSE m \in Node : TRUE][snd].account # pub
    /\ ~ \E h \in Chain(pub) : ledger[CHOOSE m \in Node : TRUE][h].prev = snd
    /\ lastHash \notin Chain(pub)
    /\ LET h == CalculateHash([account |-> pub, prev |-> snd,
                               amount |-> ledger[CHOOSE m \in Node : TRUE][snd].amount,
                               type |-> "receive", signer |-> k])
         IN /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![n][h] =
                 [account |-> pub, prev |-> snd,
                  amount |-> ledger[CHOOSE m \in Node : TRUE][snd].amount,
                  type |-> "receive", signer |-> k]]
            /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateChangeRepresentativeBlock ==
  \E k \in PrivateKey, n \in Node :
    LET pub == NodeToPublicKey[n] IN
    \E hPrev \in Chain(pub) :
      /\ lastHash \notin Chain(pub)
      /\ LET h == CalculateHash([account |-> pub, prev |-> hPrev,
                                 amount |-> 0, type |-> "changeRep", signer |-> k])
           IN /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] =
                   [account |-> pub, prev |-> hPrev, amount |-> 0,
                    type |-> "changeRep", signer |-> k]]
              /\ received' = [m \in Node |-> received[m] \cup {h}]

ProcessBlock ==
  \E n \in Node, h \in Hash :
    /\ h \in received[n]
    /\ ledger[CHOOSE m \in Node : TRUE][h] # NoBlockVal
    /\ ledger[n][h] = NoBlockVal
    /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE m \in Node : TRUE][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock
  \/ CreateSendBlock
  \/ CreateOpenBlock
  \/ CreateReceiveBlock
  \/ CreateChangeRepresentativeBlock
  \/ ProcessBlock

Spec == Init /\ [][Next]_vars

\* Signature authenticity: the block's signer must be the private key
\* that corresponds to the public key the block claims to own.
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => PrivateToPublic[ledger[n][h].signer] = ledger[n][h].account

TypeInvariant == TypeOK

====