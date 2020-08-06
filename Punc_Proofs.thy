theory Punc_Proofs
  imports Punc_Specification "General_Proofs"
begin

lemma nonempty_msg_space[simp]: "msg_space () \<noteq> {}"
  using msg_space_element by blast

lemma weight_uniform_msg_space[simp]: "weight (uniform (msg_space ())) = 1"
  by simp

lemma aux1: "x\<in>supp (uniform (msg_space ())) \<Longrightarrow> x \<in> msg_space0 ()"
  using msg_space nonempty_msg_space by auto

lemma aux2[simp]: "force_into (msg_space0 ()) puncture = puncture"
  using force_into_good puncture by fastforce

lemma aux3[simp]: "force_into (msg_space0 ()) (force_into (msg_space0 ()) m0star2) = force_into (msg_space0 ()) m0star2"
  apply (rule force_into_good)
  apply (rule force_into_bad)
  using msg_space nonempty_msg_space by auto

lemma aux4[simp]: "force_into (msg_space0 ()) (force_into (msg_space ()) m0star2) = force_into (msg_space ()) m0star2"
proof -
  have "force_into (msg_space ()) m0star2 \<in> msg_space ()"
    using nonempty_msg_space by (simp add: force_into_bad)
  then have "force_into (msg_space ()) m0star2 \<in> msg_space0 ()"
    using msg_space by auto
  then show ?thesis
    by (rule force_into_good)
qed

lemma supp_params0[simp]: "supp params0 = {()}"
  unfolding params0_def by auto

lemma supp_params[simp]: "supp params = {()}"
  unfolding params_def by simp

lemma [simp]: "params \<noteq> 0"
  using suppP_empty_simp supp_params by fastforce

lemma [simp]: "keygen () \<noteq> 0"
  unfolding keygen_def using weight_keygen0 by fastforce

end
