theory General_Proofs
  imports General_Definitions
begin

lemma force_into_good: "x : M \<Longrightarrow> force_into M x = x"
  unfolding force_into_def by simp
lemma force_into_bad: "M \<noteq> {} \<Longrightarrow> force_into M x \<in> M"
  unfolding force_into_def apply auto by (meson someI_ex)




lemma correctness_pkskm_pos[intro]:
  fixes enc dec pk sk m
  shows "correctness_pkskm p enc dec pk sk m \<ge> 0"
  unfolding correctness_pkskm_def by (fact Prob_pos)

lemma correctness_pkskm_leq1[intro]:
  fixes enc dec pk sk m
  shows "correctness_pkskm p enc dec pk sk m \<le> 1"
  unfolding correctness_pkskm_def by (fact Prob_leq1)

lemma correctness_pksk_pos[intro]:
  fixes enc dec msg_space pk sk
  assumes "msg_space p \<noteq> {}"
  assumes "finite (msg_space p)"
  shows "correctness_pksk enc dec msg_space p pk sk \<ge> 0"
proof -
  obtain m where "m : msg_space p"
    using assms by auto
  have "correctness_pksk enc dec msg_space p pk sk \<ge> correctness_pkskm enc dec p pk sk m"
    unfolding correctness_pksk_def 
    apply (rule le_cSup_finite)
    using assms \<open>m \<in> msg_space p\<close> by auto 
  then show ?thesis
    using correctness_pkskm_pos
    by (metis basic_trans_rules(23))
qed

lemma correctness_pksk_leq1[intro]:
  fixes enc dec msg_space pk sk p
  assumes "msg_space p \<noteq> {}"
  assumes "finite (msg_space p)"
  shows "correctness_pksk enc dec msg_space p pk sk \<le> 1"
  unfolding correctness_pksk_def
  apply (rule cSup_least)
  using assms by auto

lemma 
  fixes enc dec msg_space P keygen
  assumes "\<And>p. p \<in> supp P \<Longrightarrow> msg_space p \<noteq> {}"
  assumes "\<And>p. p \<in> supp P \<Longrightarrow> finite (msg_space p)"
  shows correctness_pos[intro]:  "correctness P keygen enc dec msg_space \<ge> 0"
    and correctness_leq1[intro]: "correctness P keygen enc dec msg_space \<le> 1"
proof -
  have 1: "expectation' (keygen p) (\<lambda>(xa, y). correctness_pksk enc dec msg_space p xa y) \<le> 1" if "p\<in>supp P" for p
    apply (rule expectation_upper_bound[where C=0])
      apply auto
     apply (simp add: assms correctness_pksk_pos that)
    by (simp add: assms correctness_pksk_leq1 that)
  have 0: "expectation' (keygen p) (\<lambda>(xa, y). correctness_pksk enc dec msg_space p xa y) \<ge> 0" if "p\<in>supp P" for p
    apply (rule expectation_lower_bound[where C=1])
      apply auto
     apply (simp add: assms correctness_pksk_leq1 that)
    by (simp add: assms correctness_pksk_pos that)
  show "correctness P keygen enc dec msg_space \<ge> 0"
    unfolding correctness_def
    apply (rule expectation_lower_bound[where C=1])
    using 0 1 by auto
  show "correctness P keygen enc dec msg_space \<le> 1"
    unfolding correctness_def
    apply (rule expectation_upper_bound[where C=0])
    using 0 1 by auto
qed

lemma suppP_empty_simp[simp]: "supp P = {} \<longleftrightarrow> P = 0"
  apply transfer using less_eq_real_def unfolding is_distribution_def by auto

lemma disjointnessI:
  assumes "P \<noteq> 0" and "\<And>p. p\<in>supp P \<Longrightarrow> keygen p \<noteq> 0"
  assumes "\<And>p pk sk. p\<in>supp P \<Longrightarrow> (pk,sk)\<in>supp (keygen p) \<Longrightarrow>
            Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m)) \<le> \<epsilon>"
  shows "disjointness P keygen enc fakeenc msg_space \<le> \<epsilon>"
proof -
  have sup1: "(\<Squnion>(pk, sk)\<in>supp (keygen p). Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m))) \<le> \<epsilon>" if "p\<in>supp P" for p
    apply (rule cSup_least)
    using that assms(2-3) by auto
  show ?thesis
    unfolding disjointness_def
    apply (rule cSup_least)
    using assms(1) sup1 by auto
qed

lemma disjointness_geqI:
  assumes keygen: "\<And>p. p\<in>supp P \<Longrightarrow> keygen p \<noteq> 0"
  assumes pP: "p\<in>supp P"
    and pksk: "(pk,sk)\<in>supp (keygen p)"
    and eps: "Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m)) \<ge> \<epsilon>"
  shows "disjointness P keygen enc fakeenc msg_space \<ge> \<epsilon>"
proof -
  have bdd: "bdd_above ((\<lambda>p. \<Squnion>(pk, sk)\<in>supp (keygen p).
               Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m))) ` supp P)"
    apply (rule bdd_aboveI2[where M=1])
    apply (rule cSup_least)
    using keygen by auto
  have Prob: "(\<Squnion>(pk,sk)\<in>supp (keygen p). Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m))) \<ge> \<epsilon>"
    using _ eps apply (rule cSup_upper2)
    using pksk by (auto intro: bdd_aboveI[where M=1])
  show ?thesis
    unfolding disjointness_def
    using _ Prob bdd apply (rule cSup_upper2)
    using pP by simp
qed

(* lemma disjointnessI':
  assumes "P \<noteq> 0" and "\<And>p. p\<in>supp P \<Longrightarrow> keygen p \<noteq> 0"
  assumes "\<And>p pk sk \<delta>. p\<in>supp P \<Longrightarrow> (pk,sk)\<in>supp (keygen p) \<Longrightarrow> \<delta> > 0 \<Longrightarrow>
            Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m)) \<le> \<epsilon> + \<delta>"
  shows "disjointness P keygen enc fakeenc msg_space \<le> \<epsilon>"
proof -

qed *)


lemma disjointness_leq1:
  assumes "P \<noteq> 0" and "\<And>p. p\<in>supp P \<Longrightarrow> keygen p \<noteq> 0"
  shows "disjointness P keygen enc fakeenc msg_space \<le> 1"
  apply (rule disjointnessI)
  using assms by simp_all

lemma disjointness_geq0:
  assumes "P \<noteq> 0" and "\<And>p. p\<in>supp P \<Longrightarrow> keygen p \<noteq> 0"
  shows "disjointness P keygen enc fakeenc msg_space \<ge> 0"
proof -
  from assms(1) obtain p where p: "p \<in> supp P"
    apply atomize_elim
    by (simp add: ex_in_conv)
  with assms(2) have "keygen p \<noteq> 0"
    by simp
  then obtain pk sk where pksk: "(pk,sk) \<in> supp (keygen p)"
    apply atomize_elim
    by (meson empty_iff pred_equals_eq2 suppP_empty_simp)
  show ?thesis
    using assms(2) p pksk apply (rule disjointness_geqI)
    by simp_all
qed


end
