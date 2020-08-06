theory Punc_Specification
  imports QRHL.QRHL "Base_Scheme"
begin


section \<open>Punctured scheme\<close>

(* Slight generalization wrt paper: msg_space can be a subset of msg_space0-{puncture} *)
axiomatization msg_space puncture msg_space_element where
  msg_space: "msg_space () \<subseteq> msg_space0 ()" and
  puncture: "puncture \<in> msg_space0 () - msg_space ()" and
  msg_space_element[simp]: "msg_space_element \<in> msg_space ()"

definition "params = params0"
definition "keygen = keygen0"
definition "encr = enc0r"
definition "dec P sk c = (case dec0 P sk c of Some m \<Rightarrow> if m \<in>msg_space P then Some m else None | None => None)"
definition "fakeenc _ pk = enc0 () pk puncture"
definition "enc _ pk m = map_distr (encr () pk m) (uniform UNIV)"

definition "disjointness_punc = disjointness params keygen enc fakeenc msg_space"

end
