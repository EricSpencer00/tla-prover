---- MODULE MCEcho ----
EXTENDS Echo

(* Concrete definitions used by the .cfg substitution *)
N1 == {"n1", "n2", "n3"}
I1 == "n1"
R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Specification formula required by the .cfg *)
TestSpec == (Init /\ Print(R)) /\ [][Next]_vars

====