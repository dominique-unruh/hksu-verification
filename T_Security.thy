theory T_Security
  imports T_Specification T_Proofs General_Proofs Punc_Security
begin

section \<open>Security results\<close>

lemma disjointnessT:
  shows "disjointnessT \<le> disjointness_punc"
  unfolding disjointnessT_def disjointness_punc_def
  apply (rule disjointnessI)
proof -
  fix p pk sk assume p: "p \<in> supp paramsT" and pksk: "(pk, sk) \<in> supp (keygenT p)"
  have "supp (encT G pk m) \<subseteq> supp (enc () pk m)" for G m
    unfolding encT_def enc_def encrT_def by simp
  then have "(\<Union>m\<in>msg_spaceT G. supp (encT G pk m)) \<subseteq> (\<Union>m\<in>msg_space (). supp (enc () pk m))" for G
    unfolding msg_spaceT_def by (simp add: UN_mono) 
  then have "Prob (fakeencT G pk) (\<Union>m\<in>msg_spaceT G. supp (encT G pk m))
    \<le>  Prob (fakeenc () pk) (\<Union>m\<in>msg_space (). supp (enc () pk m))" for G
    unfolding fakeencT_def by (simp add: Prob_mono)
  also have "\<dots> \<le> disjointness params keygen enc fakeenc msg_space" 
    apply (rule disjointness_geqI[where pk=pk and sk=sk and p="()"])
    using p pksk by (auto simp: keygenT_def params_def)
  finally show "Prob (fakeencT p pk) (\<Union>m\<in>msg_spaceT p. supp (encT p pk m))
       \<le> disjointness params keygen enc fakeenc msg_space".
next
  show "paramsT \<noteq> 0"
    by (metis UNIV_not_empty finite paramsT_def suppP_empty_simp supp_uniform)
qed simp

lemma disjointnessT0:
  assumes "injective_enc params0 keygen0 enc0 msg_space0"
  shows "disjointnessT = 0"
proof -
  have "disjointnessT \<le> 0"
    using disjointnessT disjointness_punc[OF assms] by simp
  moreover have "disjointnessT \<ge> 0"
    unfolding disjointnessT_def
    apply (rule disjointness_geq0)
    by auto
  ultimately show ?thesis
    by auto
qed

end
