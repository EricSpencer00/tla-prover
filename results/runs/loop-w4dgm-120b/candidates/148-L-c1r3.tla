---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Accounts == PublicKey

BlockTypes == {"genesis", "send", "open", "receive", "change"}

Blocks == [type : BlockTypes, prevHash : Hash \cup {NoHash}, from : Accounts, to : Accounts, amount : Nat, signer : PrivateKey]

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0
            ELSE LET k == CHOOSE x \in S : TRUE IN ledger[k].amount + SumOf(S \ {k})

RECURSIVE SumBalances(_)
SumBalances(S) == IF S = {} THEN 0
                  ELSE LET a == CHOOSE x \in S : TRUE IN Balance(a) + SumBalances(S \ {a})

OwnsKey(k, p) == \E q \in PrivateKey : p = q /\ k = PublicKey[q]

AccountOfRef(r) == IF r \in PublicKey THEN r ELSE ledger[r].from

Balance(a) == IF lastHash = NoHashVal THEN 0
              ELSE LET f == CHOOSE y \in Hash : ledger[y].type = "genesis" /\ ledger[y].from = a
                   IN SumOf({y \in Hash : AccountOfRef(y) = a})

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [ledger EXCEPT ![CalculateHash([type |-> "genesis", prevHash |-> NoHash, from |-> PublicKey[k], to |-> NoHash, amount |-> GenesisBalance, signer |-> k])] =
                  [type |-> "genesis", prevHash |-> NoHash, from |-> PublicKey[k], to |-> NoHash, amount |-> GenesisBalance, signer |-> k]]
  /\ lastHash' = CalculateHash([type |-> "genesis", prevHash |-> NoHash, from |-> PublicKey[k], to |-> NoHash, amount |-> GenesisBalance, signer |-> k])
  /\ received' = [n \in Node |-> [h \in Hash |-> ledger[h]]]

CreateSendBlock(n, sendAmount, rcpt) ==
  /\ \E h \in Hash : ledger[h].signer = n /\ ledger[h].type = "send"
  /\ sendAmount > 0
  /\ sendAmount <= Balance(PublicKey[n])
  /\ lastHash' = CalculateHash([type |-> "send", prevHash |-> lastHash, from |-> PublicKey[n], to |-> rcpt, amount |-> sendAmount, signer |-> n])
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [type |-> "send", prevHash |-> lastHash, from |-> PublicKey[n], to |-> rcpt, amount |-> sendAmount, signer |-> n]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

CreateOpenBlock(n, sendHash) ==
  /\ ledger[sendHash].type = "send"
  /\ ledger[sendHash].to = PublicKey[n]
  /\ lastHash' = CalculateHash([type |-> "open", prevHash |-> NoHash, from |-> PublicKey[n], to |-> NoHash, amount |-> 0, signer |-> n])
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [type |-> "open", prevHash |-> NoHash, from |-> PublicKey[n], to |-> NoHash, amount |-> 0, signer |-> n]]
  /\ received' = [g \in Node |-> received[g] \cup {lastHash'}]

CreateReceiveBlock(n, sendHash) ==
  /\ ledger[sendHash].type = "send"
  /\ ledger[sendHash].to = PublicKey[n]
  /\ lastHash' = CalculateHash([type |-> "receive", prevHash |-> lastHash, from |-> PublicKey[n], to |-> NoHash, amount |-> ledger[sendHash].amount, signer |-> n])
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [type |-> "receive", prevHash |-> lastHash, from |-> PublicKey[n], to |-> NoHash, amount |-> ledger[sendHash].amount, signer |-> n]]
  /\ received' = [g \in Node |-> received[g] \cup {lastHash'}]

CreateChangeRepBlock(n) ==
  /\ lastHash' = CalculateHash([type |-> "change", prevHash |-> lastHash, from |-> PublicKey[n], to |-> NoHash, amount |-> 0, signer |-> n])
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [type |-> "change", prevHash |-> lastHash, from |-> PublicKey[n], to |-> NoHash, amount |-> 0, signer |-> n]]
  /\ received' = [g \in Node |-> received[g] \cup {lastHash'}]

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ lastHash' = IF h > lastHash THEN h ELSE lastHash

Next ==
  \/ \E k \in PrivateKey : CreateGenesisBlock(k)
  \/ \E n \in Node, sendAmount \in 1..GenesisBalance, rcpt \in PublicKey : CreateSendBlock(n, sendAmount, rcpt)
  \/ \E n \in Node, sendHash \in Hash : CreateOpenBlock(n, sendHash)
  \/ \E n \in Node, sendHash \in Hash : CreateReceiveBlock(n, sendHash)
  \/ \E n \in Node : CreateChangeRepBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> Blocks \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
  \A h \in Hash : (ledger[h] # NoBlockVal) => OwnsKey(ledger[h].signer, ledger[h].from)

====