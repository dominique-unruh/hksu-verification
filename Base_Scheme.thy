theory Base_Scheme
  imports General_Definitions
begin

declare_variable_type pk
declare_variable_type sk
declare_variable_type msg :: finite
declare_variable_type key :: "{finite,xor_group}"
declare_variable_type ciph :: finite
declare_variable_type rand :: "{finite,xor_group}"

section \<open>Encryption scheme\<close>

definition "params0 = point_distr ()"
axiomatization keygen0 :: "unit \<Rightarrow> (pk * sk) distr" and pk_of_sk :: "sk \<Rightarrow> pk" where
  pk_of_sk: "(pk,sk) \<in> supp (keygen ()) \<Longrightarrow> pk_of_sk sk = pk"
and weight_keygen0[simp]: "weight (keygen0 ()) = 1"
axiomatization enc0r :: "unit \<Rightarrow> pk \<Rightarrow> msg \<Rightarrow> rand \<Rightarrow> ciph"
axiomatization dec0 :: "unit \<Rightarrow> sk \<Rightarrow> ciph \<Rightarrow> msg option"
axiomatization msg_space0 :: "unit \<Rightarrow> msg set" 
  where nonempty_msg_space0: "msg_space0 () \<noteq> {}"

definition "enc0 (_::unit) pk m = map_distr (enc0r () pk m) (uniform UNIV)"


section \<open>Pseudorandom function\<close>

declare_variable_type prfkey :: finite
axiomatization PRF :: "prfkey \<Rightarrow> ciph \<Rightarrow> key"
  and keygenPRF :: "prfkey distr"
  where keygenPRF_total[simp]: "weight keygenPRF = 1"

end
