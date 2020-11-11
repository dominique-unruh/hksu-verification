theory T_Proofs
  imports T_Specification "Punc_Proofs"
begin

lemma q_geq_1[simp]: "q \<ge> 1"
  unfolding q_def using qG_geq_1 qH_geq_1 by auto

lemma weight_paramsT[simp]: "weight paramsT = 1"
  unfolding paramsT_def by simp

lemma paramsT_nonzero[simp]: "paramsT \<noteq> 0"
  using weight_paramsT by force

lemma nonempty_msg_spaceT[simp]: "msg_spaceT G \<noteq> {}"
  unfolding msg_spaceT_def by simp

lemma weight_encT[simp]: "weight (encT G pk m) = 1"
  unfolding encT_def by simp

lemma supp_encT[simp]: "supp (encT G pk m) = {encrT G pk m}"
  unfolding encT_def by simp

lemma force_msg_space_element[simp]: "force_into (msg_space ()) msg_space_element = msg_space_element"
  apply (rule force_into_good) by simp

lemma program1[simplified,simp]: 
  "map_distr fst (map_distr (\<lambda>(G::msg\<Rightarrow>rand, r). (G(mstar2 := r), G, r)) (uniform UNIV)) = uniform UNIV"
proof -
  have reg: "card ((\<lambda>x. (fst x)(mstar2 := snd x)) -` {G}) = CARD(rand)" (is "card ?S = _") for G::"msg\<Rightarrow>rand"
  proof -
    define f f' where
      "f r = (G(mstar2:=r),G mstar2)" and "f' Gr = fst Gr mstar2"   
    for Gr::"(msg\<Rightarrow>rand)*rand" and r
    have inj_f': "inj_on f' ?S"
      apply (rule inj_onI)
      apply (auto simp: f'_def)
      apply (metis array_rules(5) fun_upd_triv)
      by (metis array_rules(3))
    have inj_f: "inj f"
      apply (rule injI)
      apply (auto simp: f_def)
      by (metis array_rules(3))
    show ?thesis
      using inj_f' _ inj_f apply (rule card_bij_eq[of f' _ _ f])
      by (auto simp: f_def)
  qed
  have surj: "surj (\<lambda>x. (fst x::msg\<Rightarrow>rand)(mstar2 := snd x))"
    apply (rule surjI[where f="\<lambda>G. (G,G mstar2)"]) by auto
  have "regular_betw (\<lambda>x. (fst x::msg\<Rightarrow>rand)(mstar2 := snd x)) UNIV UNIV"
    apply (rule regular_betwI[where n="CARD(rand)"])
    using surj reg by auto
  then have "map_distr (\<lambda>x. (fst x::msg\<Rightarrow>rand)(mstar2 := snd x)) (uniform UNIV) = uniform UNIV"
    by (rule map_distr_uniform_regular)
  then show ?thesis
    by (simp add: case_prod_beta)
qed

lemma program2[simplified,simp]: "map_distr snd (map_distr (\<lambda>(G, r). (G(mstar2 := r), G, r)) (uniform UNIV)) = bind_distr (uniform UNIV) (\<lambda>z. map_distr (Pair z) (uniform UNIV))"
  by (simp add: case_prod_beta)

definition "o2h_distr0 =
  bind_distr (uniform UNIV) (\<lambda>z. 
  map_distr (Pair z) (bind_distr (keygen ()) (\<lambda>za. 
  map_distr (Pair za) (bind_distr (uniform (msg_space ())) (\<lambda>zb. 
  map_distr (Pair zb) (map_distr (\<lambda>d. 
  (d, z(zb := d), (fst za, encr () (fst za) zb d), {zb})) (uniform UNIV)))))))"

lemma weight_bind_distr[simp]: 
  assumes "(weight \<mu> = 1 \<and> (\<forall>x\<in>supp \<mu>. weight (f x) = 1))"
  shows "weight (bind_distr \<mu> f) = 1"
proof (rule local_defE[of "bind_distr \<mu> f"], rename_tac B, insert assms, transfer)
  fix \<mu> :: "'a \<Rightarrow> real" and f :: "'a \<Rightarrow> 'b \<Rightarrow> real"
  assume \<mu>: "is_distribution \<mu>"
  then have \<mu>pos: "\<mu> x \<ge> 0" for x by (simp add: is_distribution_def)
  assume f: "pred_fun \<top> is_distribution f"
  then have sumf: "sum (f x) M \<le> 1" if "finite M" for x M using that apply auto
    by (meson abs_summable_on_finite is_distribution_def order_trans_rules(23) sum_leq_infsetsum top_greatest)
  assume 3: "infsetsum \<mu> UNIV = 1 \<and> (\<forall>x\<in>{x. 0 < \<mu> x}. infsetsum (f x) UNIV = 1)"
  then have weight\<mu>: "infsetsum \<mu> UNIV = 1"  by simp
  from \<mu> \<mu>pos have weightfx: "\<mu> x \<noteq> 0 \<Longrightarrow> infsetsum (f x) UNIV = 1" for x
    using 3 less_eq_real_def by auto
  fix B assume B_def: "B = (\<lambda>x. \<Sum>\<^sub>ay. \<mu> y * f y x)"
  assume B: "is_distribution B"
    (* assume 4: "(\<forall>x. 0 \<le> (\<Sum>\<^sub>ay. \<mu> y * f y x)) \<and> (\<forall>M. finite M \<longrightarrow> (\<Sum>x\<in>M. \<Sum>\<^sub>ay. \<mu> y * f y x) \<le> 1)" *)
  have \<mu>sum: "\<mu> abs_summable_on UNIV"
    using not_summable_infsetsum_eq weight\<mu> by fastforce

  have fleq1: "f x y \<le> 1" for x y
    using sumf[where M="{y}"] by simp

  have sum1: "(\<lambda>x. \<mu> x * f x y) abs_summable_on UNIV" for y
    using \<mu>sum apply (rule abs_summable_on_comparison_test'[where g=\<mu>])
    by (simp add: f[simplified, unfolded is_distribution_def] \<mu>pos fleq1 mult_left_le)
  have "(\<lambda>y. \<Sum>\<^sub>ax. \<mu> x * f x y) abs_summable_on UNIV"
    using B unfolding B_def is_distribution_def by (simp add: distr_abs_summable_on)
  then have sum2: "(\<lambda>y. \<Sum>\<^sub>ax. abs (\<mu> x * f x y)) abs_summable_on UNIV"
    using f \<mu>pos by (auto simp: is_distribution_def)
  have summable: "(\<lambda>(y, x). \<mu> x * f x y) abs_summable_on UNIV \<times> UNIV"
    apply (rule abs_summable_product')
    by (simp_all add: sum1 sum2)

  have "(\<Sum>\<^sub>ay. \<Sum>\<^sub>ax. \<mu> x * f x y) = (\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> x * f x y)"
    using summable by (rule infsetsum_swap)
  also have "\<dots> = (\<Sum>\<^sub>ax. \<mu> x * (\<Sum>\<^sub>ay. f x y))"
    apply (subst infsetsum_cmult_right; simp)
    using not_summable_infsetsum_eq weightfx by force
  also have "\<dots> = (\<Sum>\<^sub>ax. \<mu> x * 1)"
    by (rule infsetsum_cong; auto intro!: weightfx)
  also have "\<dots> = 1"
    using weight\<mu> by simp
  finally show "(\<Sum>\<^sub>ax. \<Sum>\<^sub>ay. \<mu> y * f y x) = 1" .
qed

lemmas o2h_distr0_def_sym = o2h_distr0_def[symmetric, simplified]

definition o2h_distr :: "(msg set \<times> (msg \<Rightarrow> rand) \<times> (msg \<Rightarrow> rand) \<times> pk \<times> ciph) distr" where
  "o2h_distr = map_distr (\<lambda>(G,(pk,sk),mstar,rstar,H,z,S). (S,G,H,z)) o2h_distr0"

lemma weight_o2h_distr[simp]: "weight o2h_distr = 1"
  unfolding o2h_distr_def o2h_distr0_def keygen_def by simp

lemmas case_prod_beta_abs_def = case_prod_beta[abs_def]

lemma o2h_distr_oradiff:
  assumes "(S, G, H, z) \<in> supp o2h_distr"
  assumes "x \<notin> S"
  shows "G x = H x"
  using assms unfolding o2h_distr_def o2h_distr0_def
  by (auto simp add: Let_def)

definition game2_distr :: "((msg=>rand) * (pk * sk) * msg * rand) distr" where
  "game2_distr = product_distr (uniform UNIV) (product_distr (keygen ()) (uniform (msg_space () \<times> UNIV)))"

lemmas game2_distr_def_sym = game2_distr_def[symmetric]

(* lemma game2_o2h_right_unsquashed_aux:
"(\<lambda>a. if a = mstar2 then rstar1 else G1 a) \<noteq> (\<lambda>a. if a = mstar2 then rstar2 else G2 a) \<longrightarrow> classA1 = classA2 \<longrightarrow> pk1 = tmp_pk2 \<longrightarrow> mstar1 = mstar2 \<longrightarrow> rstar1 = rstar2 \<longrightarrow> b1 = b2 \<longrightarrow> G1 = G2 \<longrightarrow> \<lbrakk>quantA1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Gin2, Gout2\<rbrakk> \<le> \<bottom>"
  by auto *)

definition game2_witness :: "(
  ((msg=>rand) * (pk * sk) * msg * rand) *
  (msg set \<times> (msg \<Rightarrow> rand) \<times> (msg \<Rightarrow> rand) \<times> pk \<times> ciph)
) distr" where
  "game2_witness = map_distr (\<lambda>(G, m, r, (pk,sk)).

    let S = {m}; c = encr () pk m r; H = G(m:=r); z = (pk,c) in
    ((G,(pk,sk),m,r),(S,G,H,z)))

  (product_distr (uniform UNIV)             \<comment> \<open>G\<close>
  (product_distr (uniform (msg_space ()))   \<comment> \<open>m\<close>
  (product_distr (uniform UNIV)             \<comment> \<open>r\<close>
                 (keygen ()))))             \<comment> \<open>(pk,sk)\<close>
"

lemma game2_witness_supp: "supp game2_witness \<subseteq> {((G1,(pk1,sk1),mstar1,rstar1), (S2,G2,H2,z2)).
      G1(mstar1:=rstar1) = H2 \<and> pk1=fst z2 \<and> encr () pk1 mstar1 rstar1 = snd z2}" 
  unfolding game2_witness_def
  by auto

lemma leq_INFv[simp]:
  fixes V :: "'a \<Rightarrow> 'b subspace"
  shows "(A \<le> (INF x\<in>M. V x)) = (\<forall>x\<in>M. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma triangle: "abs(a-b) \<le> (x::real) \<Longrightarrow> abs(b-c) \<le> y \<Longrightarrow> abs(c-a) \<le> x+y"
  by simp

lemma abs_leq: "p5 \<le> x \<Longrightarrow> abs(p4-p5) \<le> y \<Longrightarrow> p4 \<le> y + x" for x::real
  by simp

lemma combine_bounds: (* ds_encT_real = game1, game1=game2, ds_encT_fake=game0 *)
  assumes "Q\<ge>0"
  assumes g45: "abs(game4 - game5) \<le> abs(indcpa_enc_0 - indcpa_enc_1)"
  assumes g5: "game5 <= R"
  assumes g3r: "abs ( game3 - ds_encT_real ) <= 2 * sqrt( Q * game4 )"
  assumes fg3: "abs(ds_encT_fake - game3) \<le> abs(ds_enc_real - ds_enc_fake)"
  shows "abs(ds_encT_real - ds_encT_fake) 
   \<le> abs(ds_enc_real - ds_enc_fake)
         + 2 * sqrt Q * sqrt( abs(indcpa_enc_0 - indcpa_enc_1) + R )"
    (is "_ \<le> ?rhs")
proof -
  from g3r fg3 have "abs(ds_encT_real - ds_encT_fake) \<le> 
    abs(ds_enc_real - ds_enc_fake) + 2 * sqrt( Q * game4 )" (is "_ \<le> ?rhs'")
    by linarith
  also
  from g45 g5 have "game4 \<le> abs(indcpa_enc_0 - indcpa_enc_1) + R"
    by linarith
  with \<open>Q\<ge>0\<close> have "?rhs' \<le> ?rhs"
    unfolding real_sqrt_mult
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono)
  finally show ?thesis by assumption
qed

(* Copied from the result of applying squash left a number of times *)
definition scs_distr0 :: "((msg\<Rightarrow>rand) \<times> (pk \<times> sk) \<times> msg \<times> rand \<times> (pk \<times> ciph) \<times> msg set) distr" where "scs_distr0 = 
  product_distr (uniform UNIV) (bind_distr (keygen ()) (\<lambda>z. map_distr (Pair z) (bind_distr (uniform (msg_space ())) (\<lambda>za. map_distr (Pair za) (map_distr (\<lambda>d. (d, (fst z, encr () (fst z) msg_space_element d), {za})) (uniform UNIV))))))"

lemmas scs_distr0_def_sym = scs_distr0_def[symmetric, simplified]

definition "scs_distr = map_distr (\<lambda>(G,(tmp_pk,sk),tmp_mstar,rstar,z,S). (S,G,z)) scs_distr0"

definition "swap guess z = (if guess\<notin>msg_space() then z else if z=guess then msg_space_element else if z=msg_space_element then guess else z)"
  for swap

lemma [simp]: "map_distr (swap guess) (uniform (msg_space ())) = uniform (msg_space ())"
proof -
  have [simp]: "swap guess \<in> msg_space () \<rightarrow> msg_space ()"
    by (auto simp: swap_def)
  have [simp]: "x \<in> msg_space () \<Longrightarrow> swap guess (swap guess x) = x" for x
    by (auto simp: swap_def)
  show ?thesis
    apply (rule map_distr_uniform)
    by (rule bij_betwI[where g="swap guess"], auto)
qed

lemma [simp]: "guess1 \<in> msg_space () \<longrightarrow> swap guess1 guess1 = msg_space_element"
  unfolding swap_def by simp

lemma [simp]: "{..<q}\<noteq>{}"
  using q_geq_1
  by (simp add: lessThan_empty_iff)

lemma [simp]: "weight (keygen ()) = 1"
  by (simp add: keygen_def)

(* Tactic for that? *)
lemma guessing_prob: 
  "probability (expression \<lbrakk>m\<rbrakk> (\<lambda>m. m = x)) (block [sample \<lbrakk>m\<rbrakk> (const_expression (uniform M))]) rho
  = (if x\<in>M then 1 / real (card M) else 0)"
  apply (subst probability_sample)
  apply transfer by simp


lemma [simp]: "weight scs_distr0 = 1"
  unfolding scs_distr0_def by simp

lemma [simp]: "weight scs_distr = 1"
  unfolding scs_distr_def by simp

    

(* lemma eigenspace_lift[simp]:
  assumes [simp]: "distinct_qvars Q"
  shows "eigenspace c (A\<guillemotright>Q) = (eigenspace c A)\<guillemotright>Q"
  unfolding eigenspace_def
  apply (rewrite at idOp to "idOp\<guillemotright>Q" lift_idOp[symmetric])
  by (simp del: lift_idOp) *)




lemma divide_tmp_Gout:
  assumes [simp]: "declared_qvars \<lbrakk>Gin1,Gin2,Gout1,Gout2,quantA1,quantA2,Hin1,Hout1,Hin2,Hout2,tmp_Gout1,tmp_Gout2\<rbrakk>"
  shows "Span {ket 0}\<guillemotright>\<lbrakk>tmp_Gout2\<rbrakk> \<sqinter> (\<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk> \<sqinter> Span {ket 0}\<guillemotright>\<lbrakk>tmp_Gout1\<rbrakk>)
          \<le> \<lbrakk>tmp_Gout1, quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>tmp_Gout2, quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
    (is "?lhs \<le> ?rhs") 
proof -
  have "Span {ket 0}\<guillemotright>\<lbrakk>tmp_Gout1\<rbrakk> \<sqinter> Span {ket 0}\<guillemotright>\<lbrakk>tmp_Gout2\<rbrakk> = \<lbrakk>tmp_Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>tmp_Gout2\<rbrakk> \<sqinter> Span {ket 0}\<guillemotright>\<lbrakk>tmp_Gout1\<rbrakk>"
    apply (subst quantum_eq_unique) by auto
  also have "\<dots> \<le> \<lbrakk>tmp_Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>tmp_Gout2\<rbrakk>"
    using inf.cobounded1 by blast
  finally have "?lhs \<le> \<lbrakk>tmp_Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>tmp_Gout2\<rbrakk> \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
    by (smt inf.bounded_iff inf.cobounded1 inf.coboundedI2 inf_commute inf_left_commute)
  also have "\<dots> \<le> ?rhs"
    apply (rule order_trans)
     apply (rule quantum_equality_merge, simp)
    by simp
  finally show ?thesis by -
qed

lemma weight_keygen[simp]: "weight (keygen p) = 1"
  by simp

lemma weight_keygenT[simp]: "weight (keygenT p) = 1"
  unfolding keygenT_def by simp

lemma [simp]: "keygen p \<noteq> 0"
  using weight_keygen Prob_0
  by fastforce 

lemma [simp]: "keygenT p \<noteq> 0"
  unfolding keygenT_def by simp

lemma [simp]: "q \<noteq> 0"
  using q_geq_1 by auto

end
