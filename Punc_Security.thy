theory Punc_Security
  imports Punc_Proofs
begin

section \<open>Security results\<close>

(* Lemma 3.1, first part *)
lemma correctness_punc:
  "correctness params keygen enc dec msg_space \<le> correctness params0 keygen0 enc0 dec0 msg_space0"
  (is "?lhs \<le> ?rhs")
proof -
  have ex1: "expectation_exists' (keygen0 ()) (\<lambda>(x, y). correctness_pksk enc dec0 msg_space () x y)"
    apply (rule expectation_exists_bounded[where a=0 and b=1])
    by (auto simp: case_prod_beta)
  have ex2: "expectation_exists' (keygen0 ()) (\<lambda>(x, y). correctness_pksk enc0 dec0 msg_space0 () x y)"
    apply (rule expectation_exists_bounded[where a=0 and b=1])
    by (auto simp: nonempty_msg_space0 case_prod_beta)
  have "?lhs = correctness params keygen enc dec0 msg_space"
  proof -
    have "(case dec0 () sk c of None \<Rightarrow> None | Some m \<Rightarrow> if m \<in> msg_space p then Some m else None) \<noteq> Some m
      \<longleftrightarrow> dec0 () sk c \<noteq> Some m" if "m \<in> msg_space p" for p sk m c
      using that apply (cases "dec0 () sk c") by auto
    then have "correctness_pkskm enc dec p pk sk m = correctness_pkskm enc dec0 p pk sk m" if "m \<in> msg_space p" for p pk sk m
      using that unfolding correctness_pkskm_def dec_def unit_eq by auto
    then show ?thesis
      unfolding correctness_def correctness_pksk_def by auto
  qed
  also have "\<dots> \<le> ?rhs"
    unfolding correctness_def keygen_def
    unfolding params0_def params_def expectation_point_distr
    apply simp
    using ex1 ex2 apply (rule expectation_mono, simp add: case_prod_beta)
    unfolding correctness_pksk_def
    using nonempty_msg_space _ msg_space apply (rule cSUP_subset_mono)
    unfolding enc_def encr_def enc0_def by auto
  finally show ?thesis by -
qed

(* Lemma 3.1, third part *)
lemma disjointness_punc:
  assumes "injective_enc params0 keygen0 enc0 msg_space0"
  shows "disjointness_punc = 0"
proof -
  have prob: "Prob (fakeenc () pk) (\<Union>m\<in>msg_space (). supp (enc () pk m)) \<le> 0" if "(pk,sk) \<in> supp (keygen p)" for pk sk p
  proof -
    from assms that have "injective_enc_pk () enc0 msg_space0 pk"
      unfolding injective_enc_def keygen_def by auto
    then have "disjnt (supp (enc0 () pk puncture)) (supp (enc0 () pk m2))" if "m2\<in>msg_space0 ()" for m2
      unfolding injective_enc_pk_def using puncture that by auto
    then have "disjnt (supp (fakeenc () pk)) (supp (enc () pk m2))" if "m2\<in>msg_space ()" for m2
      unfolding fakeenc_def enc_def enc0_def encr_def using that msg_space by auto
    then have disjnt: "disjnt (supp (fakeenc () pk)) (\<Union>x\<in>msg_space (). supp (enc () pk x))"
      using disjoint_UN_iff by blast
    show "Prob (fakeenc () pk) (\<Union>m\<in>msg_space (). supp (enc () pk m)) \<le> 0"
      apply (rule eq_refl, subst Prob_is_0)
      using disjnt by assumption
  qed
  have "disjointness params keygen enc fakeenc msg_space \<le> 0"
    unfolding disjointness_def 
    apply (rule cSUP_least, simp)
    apply (rule cSUP_least, simp)
    using prob by auto
  moreover have "disjointness params keygen enc fakeenc msg_space \<ge> 0"
    apply (rule disjointness_geq0)
    by auto
  ultimately show ?thesis
    unfolding disjointness_punc_def
    by simp
qed 

end
