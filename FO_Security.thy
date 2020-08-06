theory FO_Security
  imports FO_Specification "General_Proofs" Punc_Proofs
begin               

section \<open>Security results\<close>

lemma
  shows "KEMcorrectness paramsFO keyspaceFO keygenFO encapsFO decapsFO \<le> correctness paramsT keygenT encT decT msg_spaceT"
proof -
  define KEMcorr where "KEMcorr p pk sk = prob (map_distr (\<lambda>(K, c). decapsFO p sk c \<noteq> Some K \<or> K \<notin> keyspaceFO p) (encapsFO p pk)) True"
    for p pk sk

  have KEMcorr_leq1: "KEMcorr p pk sk \<le> 1" for p pk sk
    unfolding KEMcorr_def by simp
  have KEMcorr_geq0: "KEMcorr p pk sk \<ge> 0" for p pk sk
    unfolding KEMcorr_def by simp

  have correctness_pksk: "correctness_pksk encT decT msg_spaceT G pk sk = (if (\<exists>m\<in>msg_spaceT G. decT G sk (encrT G pk m) \<noteq> Some m) then 1 else 0)" for G pk sk
    unfolding correctness_pksk_def correctness_pkskm_def encT_def
    apply (subst cSup_eq_Max)
      apply (auto simp: msg_spaceT_def)
    apply (smt Max_ge Max_in equals0D finite finite_imageI image_iff indicator_def mem_Collect_eq)
    by (metis (mono_tags, lifting) Max_in finite finite_imageI imageE image_is_empty msg_spaceT_def nonempty_msg_space)

  have KEMcorr_good: "KEMcorr (G, H) pk (sk, prfk) = 0" if "\<And>m. m\<in>msg_spaceT G \<Longrightarrow> decT G sk (encrT G pk m) = Some m"
    for G H pk sk prfk
    unfolding KEMcorr_def encapsFO_def
    apply (subst Prob_singleton[symmetric])
    apply (subst Prob_map_distr')+
    apply (rule Prob_is_0[THEN iffD2])
    unfolding disjnt_def
    apply (subst supp_uniform, simp add: msg_spaceT_def, simp)
    unfolding  encapsrFO_def decapsFO_def keyspaceFO_def
    by (auto simp: that)

  have KEMcorr_leq: "KEMcorr (G,H) pk (sk,prfk) \<le> correctness_pksk encT decT msg_spaceT G pk sk" for G H pk sk prfk
    unfolding correctness_pksk
    apply (cases "\<exists>m\<in>msg_spaceT G. decT G sk (encrT G pk m) \<noteq> Some m")
     apply auto
     apply (simp add: KEMcorr_def)
    using KEMcorr_good by simp 

  have KEMcorrectness: "KEMcorrectness paramsFO keyspaceFO keygenFO encapsFO decapsFO
    = expectation' paramsFO (\<lambda>p. 
      expectation' (keygenFO p) (\<lambda>(pk,sk). 
      KEMcorr p pk sk))"
    unfolding KEMcorrectness_def
    apply (subst prob_expectation)
    apply (subst prob_expectation)
    unfolding case_prod_beta KEMcorr_def by auto

  have paramsFO_def': "paramsFO = product_distr (uniform UNIV) (uniform UNIV)"
    unfolding paramsFO_def by auto

  have ee1: "expectation_exists' paramsFO (\<lambda>p. expectation' (keygenFO p) (\<lambda>(x, y). KEMcorr p x y))"
    unfolding case_prod_beta
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
     apply (rule expectation'_lower_bound[where C=1])
       apply simp
      apply (rule KEMcorr_leq1)
     apply (rule KEMcorr_geq0)
    apply (rule expectation'_upper_bound[where C=0])
      apply simp
     apply (rule KEMcorr_geq0)
    by (rule KEMcorr_leq1)
  have ee2: "expectation_exists' paramsFO
     (\<lambda>(G, H). expectation' (keygenFO (G, H)) (\<lambda>(pk, sk, prfk). correctness_pksk encT decT msg_spaceT G pk sk))"
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
    unfolding case_prod_beta
     apply (rule expectation'_lower_bound[where C=1])
       apply simp
      apply (simp add: correctness_pksk)
     apply (simp add: correctness_pksk)
    apply (rule expectation'_upper_bound[where C=0])
      apply simp
     apply (simp add: correctness_pksk)
    by (simp add: correctness_pksk)
  have ee3: "expectation_exists' (keygenFO x) (\<lambda>p. KEMcorr x (fst p) (snd p))" for x
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
     apply (rule KEMcorr_geq0)
    by (rule KEMcorr_leq1)
  have ee4: "expectation_exists' (keygenFO x) (\<lambda>p. correctness_pksk encT decT msg_spaceT (fst x) (fst p) (fst (snd p)))" for x
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
     apply (simp add: correctness_pksk)
    by (simp add: correctness_pksk)
  have ee5: "expectation_exists' (keygenT G) (\<lambda>a. correctness_pksk encT decT msg_spaceT G (fst a) (snd a))" for G
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
     apply (simp add: correctness_pksk)
    by (simp add: correctness_pksk)
  have ee6: "expectation_exists' (uniform UNIV)
     (\<lambda>a. expectation' (keygenT a) (\<lambda>b. correctness_pksk encT decT msg_spaceT a (fst b) (snd b)))"
    apply (rule expectation_exists'_bounded[where a=0 and b=1])
     apply (rule expectation'_lower_bound[where C=1])
       apply simp
      apply (simp add: correctness_pksk)
     apply (simp add: correctness_pksk)
    apply (rule expectation'_upper_bound[where C=0])
      apply simp
     apply (simp add: correctness_pksk)
    by (simp add: correctness_pksk)

  have correctness: "correctness paramsT keygenT encT decT msg_spaceT =
    expectation' (paramsFO) (\<lambda>(G,H::msg\<Rightarrow>key). 
    expectation' (keygenFO (G,H)) (\<lambda>(pk, (sk, prfk)). correctness_pksk encT decT msg_spaceT G pk sk))"
    unfolding correctness_def paramsFO_def' paramsT_def keygenFO_def 
    apply (simp add: case_prod_beta del: product_distr_uniform)
    apply (subst expectation'_product_distr1'')
     apply (rule ee5)
    apply (simp add: case_prod_beta del: product_distr_uniform)
    unfolding case_prod_beta
    apply (subst expectation'_product_distr1'')
     apply (rule ee6)
    by simp

  show ?thesis
    unfolding KEMcorrectness correctness
    using ee1 ee2 apply (rule expectation_mono)
    unfolding case_prod_beta prod.collapse
    using ee3 ee4 apply (rule expectation_mono)
    using KEMcorr_leq by auto
qed

end
