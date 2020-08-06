theory T_Specification
imports "Punc_Specification"
begin

section \<open>Transformation T\<close>

\<comment> \<open>Public parameters of T[...] consist of a random oracle \<^term>\<open>G::msg\<Rightarrow>rand\<close>\<close>
definition paramsT :: "(msg\<Rightarrow>rand) distr" where "paramsT = uniform UNIV"
definition "keygenT G = keygen ()" for G :: "msg\<Rightarrow>rand"
definition "encrT G pk m = encr () pk m (G m)"
definition "encT G pk m = point_distr (encrT G pk m)"
definition "decT G sk c = (case dec () sk c of
  None \<Rightarrow> None
| Some m \<Rightarrow> if encrT G (pk_of_sk sk) m = c then Some m else None)"
definition "fakeencT G = fakeenc ()" for G :: "msg\<Rightarrow>rand"
definition "msg_spaceT G = msg_space ()" for G :: "msg\<Rightarrow>rand"

definition "disjointnessT = disjointness paramsT keygenT encT fakeencT msg_spaceT"

end
