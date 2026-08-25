---- MODULE MCEcho ----
EXTENDS Echo

(* Concrete finite instances used by the .cfg substitutions *)
N1 == {"n1", "n2", "n3"}

I1 == "n1"

R1 == {
        << "n1", "n2" >>, << "n2", "n1" >>,
        << "n1", "n3" >>, << "n3", "n1" >>,
        << "n2", "n3" >>, << "n3", "n2" >>
      }

(* Alias to the specification defined in Echo *)
TestSpec == Spec

====