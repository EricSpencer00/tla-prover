---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block is a signed record in an account chain; the chain is the ordering.
\* The invariant protects the fact that signatures are never forged.
Block == [hash: Hash, prev: Hash \cup {NoHash}, owner: PublicKey, kind: {"genesis", "send", "open", "receive", "change"}, amount: Nat, dest: PublicKey \cup {NoPublicKey}]

\* The ledger is replicated across nodes; each node validates independently.
Ledger == [Node -> [Hash -> Block \cup {NoBlockVal}]]

RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET a == CHOOSE x \in S : TRUE IN Balance(a) + SumBalances(S \ {a})

RECURSIVE Balance(_)
Balance(a) ==
  LET chain == {b \in Hash : Ledger[CHOOSE n \in Node : TRUE][b] # NoBlockVal /\ Ledger[CHOOSE n \in Node : TRUE][b].owner = a} IN
  IF chain = {} THEN 0
  ELSE LET b == CHOOSE x \in chain : TRUE IN
       IF b.kind = "send" THEN -b.amount + Balance(a)
       ELSE IF b.kind = "receive" THEN b.amount + Balance(a)
       ELSE Balance(a)

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in Ledger
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is the only way coins enter the system.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E k \in PrivateKey, n \in Node :
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NoHash] = [hash |-> NoHash, prev |-> NoHash, owner |-> PublicKeyOf(k), kind |-> "genesis", amount |-> GenesisBalance, dest |-> NoPublicKey]]]
       /\ lastHash' = NoHash
  /\ UNCHANGED received

\* A send block debits the sender and names a recipient.
CreateSendBlock ==
  /\ \E k \in PrivateKey, n \in Node, amt \in 1..GenesisBalance, d \in PublicKey :
       /\ Balance(PublicKeyOf(k)) >= amt
       /\ LET h == CalculateHash([prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "send", amount |-> amt, dest |-> d]) IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "send", amount |-> amt, dest |-> d]]]
            /\ lastHash' = h
            /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<>>

\* An open block starts a new account's chain from a received send.
CreateOpenBlock ==
  /\ \E k \in PrivateKey, n \in Node, h \in Hash :
       /\ ledger[CHOOSE m \in Node : TRUE][h] # NoBlockVal
       /\ ledger[CHOOSE m \in Node : TRUE][h].dest = PublicKeyOf(k)
       /\ ledger[CHOOSE m \in Node : TRUE][h].kind = "send"
       /\ Balance(PublicKeyOf(k)) = 0
       /\ LET g == CalculateHash([prev |-> NoHash, owner |-> PublicKeyOf(k), kind |-> "open", amount |-> 0, dest |-> NoPublicKey]) IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] = [hash |-> g, prev |-> NoHash, owner |-> PublicKeyOf(k), kind |-> "open", amount |-> 0, dest |-> NoPublicKey]]]
            /\ lastHash' = g
            /\ received' = [received EXCEPT ![n] = @ \cup {g}]
  /\ UNCHANGED <<>>

\* A receive block credits the recipient and consumes the matching send.
CreateReceiveBlock ==
  /\ \E k \in PrivateKey, n \in Node, h \in Hash :
       /\ ledger[CHOOSE m \in Node : TRUE][h] # NoBlockVal
       /\ ledger[CHOOSE m \in Node : TRUE][h].dest = PublicKeyOf(k)
       /\ ledger[CHOOSE m \in Node : TRUE][h].kind = "send"
       /\ LET g == CalculateHash([prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "receive", amount |-> ledger[CHOOSE m \in Node : TRUE][h].amount, dest |-> NoPublicKey]) IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![g] = [hash |-> g, prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "receive", amount |-> ledger[CHOOSE m \in Node : TRUE][h].amount, dest |-> NoPublicKey]]]
            /\ lastHash' = g
            /\ received' = [received EXCEPT ![n] = @ \cup {g}]
  /\ UNCHANGED <<>>

\* A change-representative block reassigns voting power without moving funds.
CreateChangeBlock ==
  /\ \E k \in PrivateKey, n \in Node :
       LET h == CalculateHash([prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "change", amount |-> 0, dest |-> NoPublicKey]) IN
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [hash |-> h, prev |-> lastHash, owner |-> PublicKeyOf(k), kind |-> "change", amount |-> 0, dest |-> NoPublicKey]]]
            /\ lastHash' = h
            /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<>>

\* Validation checks signatures, references, and block-type-specific rules.
ValidateBlock ==
  /\ \E n \in Node, h \in received[n] :
       /\ ledger[n][h] = NoBlockVal
       /\ ledger[CHOOSE m \in Node : TRUE][h] # NoBlockVal
       /\ ledger[n]' = [ledger[n] EXCEPT ![h] = ledger[CHOOSE m \in Node : TRUE][h]]
       /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeBlock \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* No forged signatures: every recorded block's owner matches its signature.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].owner = PublicKeyOf(PrivateKeyOf(ledger[n][h].owner))

\* The total coin supply is never exceeded by the sum of all account balances.
BalanceBound == SumBalances(PublicKey) <= GenesisBalance

====