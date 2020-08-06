theory FO_Specification
  imports "T_Specification"
begin

section \<open>Transformation T\<close>

type_synonym skfo = "sk * prfkey"

text \<open>We deviate from AKE paper by using a PRF instead of a private oracle Hr\<close>

\<comment> \<open>Public parameters of T[...] consist of a random oracle \<^term>\<open>G::msg\<Rightarrow>rand\<close>\<close>
definition paramsFO :: "((msg\<Rightarrow>rand) * (msg\<Rightarrow>key)) distr" where "paramsFO = uniform UNIV"
definition keyspaceFO :: "((msg\<Rightarrow>rand) * (msg\<Rightarrow>key)) \<Rightarrow> key set" where "keyspaceFO _ = UNIV"
definition "keygenFO = (\<lambda>(G,H::msg\<Rightarrow>key). map_distr (\<lambda>((pk,sk),prfk). (pk,(sk,prfk))) (product_distr (keygenT G) keygenPRF))"
definition "encapsrFO = (\<lambda>(G,H::msg\<Rightarrow>key) pk r. (H(r), encrT G pk r))"
definition "encapsFO GH pk = map_distr (encapsrFO GH pk) (uniform (msg_spaceT (fst GH)))"
definition "decapsFO = (\<lambda>(G,H) (sk,prfk) c. case decT G sk c of None \<Rightarrow> Some (PRF prfk c) | Some m \<Rightarrow> Some(H(m)))"
  \<comment> \<open>Note: we define the output of \<^const>\<open>decapsFO\<close> as key option even though \<^const>\<open>decapsFO\<close> is total. For compatibility with other, non-total schemes.\<close>

axiomatization where
  enc0_injective: "injective_enc params0 keygen0 enc0 msg_space0"

end
