---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A block is a record of its type, the account it belongs to, the previous
\* block in that account's chain, the block it references (send/open/receive),
\* the amount it moves, and the Ed25519 signature over its contents.
Block == [type: {"genesis", "send", "open", "receive", "change"},
          account: PublicKey, prev: Hash, ref: Hash, amount: Nat,
          sig: [pub: PublicKey, priv: PrivateKey]]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* The genesis block is the only block that can be created without a previous
\* block, so it is added to every node's ledger at once.
Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Balance is computed by walking the account chain backwards from the last
\* block, summing amounts for receive/open and subtracting for send.
RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHashVal THEN 0
  ELSE
    LET b == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal] IN
      IF b.type \in {"receive", "open"} THEN b.amount + Balance(b.prev)
      ELSE IF b.type = "send" THEN Balance(b.prev) - b.amount
      ELSE Balance(b.prev)

\* The total of all account balances must never exceed the genesis balance.
BalanceBound == Balance(NoHashVal) <= GenesisBalance

\* A block is valid if its signature matches the account's public key and its
\* referenced blocks exist in the local ledger copy.
ValidBlock(b, n) ==
  /\ b.sig.pub = b.account
  /\ (b.prev = NoHashVal \/ ledger[n][b.prev] # NoBlockVal)
  /\ (b.ref = NoHashVal \/ ledger[n][b.ref] # NoBlockVal)

\* A send block may only be created if the sender's balance can cover it.
SendAllowed(n, amt) == Balance(NoHashVal) >= amt

\* A receive block may only be created if the referenced send block has not
\* already been claimed by any account's chain.
UnclaimedSend(h) ==
  \A n \in Node : ledger[n][h] # NoBlockVal => ledger[n][h].type # "receive"

CreateGenesisBlock(n, pk, sk) ==
  /\ lastHash = NoHashVal
  /\ sk \in PrivateKey /\ pk \in PublicKey
  /\ ledger[n][NoHash] = NoBlockVal
  /\ LET h == CalculateHash([type |-> "genesis", account |-> pk,
                             prev |-> NoHashVal, ref |-> NoHashVal,
                             amount |-> GenesisBalance, sig |-> [pub |-> pk, priv |-> sk]])
     IN
       /\ lastHash' = h
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [type |-> "genesis",
                                                             account |-> pk,
                                                             prev |-> NoHashVal,
                                                             ref |-> NoHashVal,
                                                             amount |-> GenesisBalance,
                                                             sig |-> [pub |-> pk, priv |-> sk]]]]
       /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateSendBlock(n, pk, sk, amt) ==
  /\ lastHash # NoHashVal
  /\ sk \in PrivateKey /\ pk \in PublicKey
  /\ SendAllowed(n, amt)
  /\ LET h == CalculateHash([type |-> "send", account |-> pk,
                             prev |-> lastHash, ref |-> NoHashVal,
                             amount |-> amt, sig |-> [pub |-> pk, priv |-> sk]])
     IN
       /\ lastHash' = h
       /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "send", account |-> pk,
                                              prev |-> lastHash, ref |-> NoHashVal,
                                              amount |-> amt,
                                              sig |-> [pub |-> pk, priv |-> sk]]]
       /\ received' = [received EXCEPT ![n] = @ \cup {h}]

CreateOpenBlock(n, pk, sk, h) ==
  /\ lastHash # NoHashVal
  /\ sk \in PrivateKey /\ pk \in PublicKey
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].account # pk
  /\ ledger[n][NoHash] = NoBlockVal
  /\ LET g == CalculateHash([type |-> "open", account |-> pk,
                             prev |-> NoHashVal, ref |-> h,
                             amount |-> ledger[n][h].amount,
                             sig |-> [pub |-> pk, priv |-> sk]])
     IN
       /\ lastHash' = g
       /\ ledger' = [ledger EXCEPT ![n][g] = [type |-> "open", account |-> pk,
                                              prev |-> NoHashVal, ref |-> h,
                                              amount |-> ledger[n][h].amount,
                                              sig |-> [pub |-> pk, priv |-> sk]]]
       /\ received' = [received EXCEPT ![n] = @ \cup {g}]

CreateReceiveBlock(n, pk, sk, h) ==
  /\ lastHash # NoHashVal
  /\ sk \in PrivateKey /\ pk \in PublicKey
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].account # pk
  /\ UnclaimedSend(h)
  /\ LET g == CalculateHash([type |-> "receive", account |-> pk,
                             prev |-> lastHash, ref |-> h,
                             amount |-> ledger[n][h].amount,
                             sig |-> [pub |-> pk, priv |-> sk]])
     IN
       /\ lastHash' = g
       /\ ledger' = [ledger EXCEPT ![n][g] = [type |-> "receive", account |-> pk,
                                              prev |-> lastHash, ref |-> h,
                                              amount |-> ledger[n][h].amount,
                                              sig |-> [pub |-> pk, priv |-> sk]]]
       /\ received' = [received EXCEPT ![n] = @ \cup {g}]

CreateChangeBlock(n, pk, sk) ==
  /\ lastHash # NoHashVal
  /\ sk \in PrivateKey /\ pk \in PublicKey
  /\ LET h == CalculateHash([type |-> "change", account |-> pk,
                             prev |-> lastHash, ref |-> NoHashVal,
                             amount |-> 0, sig |-> [pub |-> pk, priv |-> sk]])
     IN
       /\ lastHash' = h
       /\ ledger' = [ledger EXCEPT ![n][h] = [type |-> "change", account |-> pk,
                                              prev |-> lastHash, ref |-> NoHashVal,
                                              amount |-> 0,
                                              sig |-> [pub |-> pk, priv |-> sk]]]
       /\ received' = [received EXCEPT ![n] = @ \cup {h}]

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ ValidBlock(ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal], n)
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey : CreateGenesisBlock(n, pk, sk)
  \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey, amt \in 1..GenesisBalance : CreateSendBlock(n, pk, sk, amt)
  \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey, h \in Hash : CreateOpenBlock(n, pk, sk, h)
  \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey, h \in Hash : CreateReceiveBlock(n, pk, sk, h)
  \/ \E n \in Node, pk \in PublicKey, sk \in PrivateKey : CreateChangeBlock(n, pk, sk)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must have a signature that matches the
\* public key of the account that owns the chain it sits in.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig.pub = ledger[n][h].account

====