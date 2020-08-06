theory FO_Proofs_Very_Slow
  imports FO_Proofs0
begin

(* This file contains a proof that runs *very* slowly.
   Since this file will be loaded each time qrhl-tool starts up,
   we have commented the proof out and replaced it by "sorry".
   To check the proof, simply remove the "sorry" and comment the 
   proof back in. *)

lemma queryH_invariant_vc:
  fixes Hq1 :: "ciph \<Rightarrow> key" and H1 :: "msg \<Rightarrow> key"
  assumes [simp]: "declared_qvars \<lbrakk>Gin1,tmp_Gin2,Gout1,tmp_Gout2,quantA1,quantA2,Hin1,Hout1,Hin2,Hout2,Gin2,Gout2\<rbrakk>"
  (* Copy & paste of subgoal in QRHL tool *)
  shows "\<CC>\<ll>\<aa>[H1 = mk_Hq Hq2 H02 G2 pk2] \<sqinter> 
(Uoracle H1\<guillemotright>\<lbrakk>Hin1, Hout1\<rbrakk> \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> 
\<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>) \<sqinter> Span {ket 0}\<guillemotright>\<lbrakk>Gout2\<rbrakk> \<le> \<CC>\<ll>\<aa>[isometry comm_op] \<sqinter> 
((comm_op\<guillemotright>\<lbrakk>Hin2, Gin2\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry (Uoracle G2)] \<sqinter> ((Uoracle G2\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk>)* \<cdot> 
(\<CC>\<ll>\<aa>[isometry (Uoracle (\<lambda>(m, g). mk_Hq' Hq2 H02 g pk2 m))] \<sqinter> ((Uoracle (\<lambda>(m, g). mk_Hq' 
Hq2 H02 g pk2 m)\<guillemotright>variable_concat \<lbrakk>Gin2, Gout2\<rbrakk> \<lbrakk>Hout2\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry (Uoracle G2)] \<sqinter> 
((Uoracle G2\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk>)* \<cdot> (\<CC>\<ll>\<aa>[isometry comm_op] \<sqinter> ((comm_op\<guillemotright>\<lbrakk>Hin2, Gin2\<rbrakk>)* \<cdot> 
(\<CC>\<ll>\<aa>[H1 = mk_Hq Hq2 H02 G2 pk2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> 
\<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk> \<sqinter> (comm_op\<guillemotright>\<lbrakk>Hin2, Gin2\<rbrakk> \<cdot> \<top>))) \<sqinter> 
(Uoracle G2\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> \<cdot> \<top>))) \<sqinter> (Uoracle (\<lambda>(m, g). mk_Hq' Hq2 H02 g pk2 m)\<guillemotright>variable_concat
 \<lbrakk>Gin2, Gout2\<rbrakk> \<lbrakk>Hout2\<rbrakk> \<cdot> \<top>))) \<sqinter> (Uoracle G2\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> \<cdot> \<top>))) \<sqinter> (comm_op\<guillemotright>\<lbrakk>Hin2, Gin2\<rbrakk> \<cdot> \<top>)))"
    (is "Cla[?class] \<sqinter> _ \<sqinter> _ \<le> ?post")

  sorry

(*
  
proof (cases ?class)
  case True
  (* define cla where "cla = ((classA1, c1, K'1, b1, in_pk1, in_cstar1, Kstar1) = (classA2, c2, K'2, b2, in_pk2, in_cstar2, Kstar2) \<and> G1 = G2 \<and> H1 = (\<lambda>m. Hq2 (encrT G2 pk2 m)) \<and> Hq1 = Hq2 \<and> cstar1 = adv_cstar2)" *)
  define h1 where "h1 = Uoracle H1\<guillemotright>\<lbrakk>Hin1, Hout1\<rbrakk>"
  define qeq where "qeq = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>"
  define ket0 where "ket0 = Span {ket 0}\<guillemotright>\<lbrakk>Gout2\<rbrakk>"

  obtain UoracleH where UoracleH1: "Uoracle H1\<guillemotright>\<lbrakk>Hin1, Hout1\<rbrakk> = UoracleH\<guillemotright>\<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk>"
    and UoracleH2: "Uoracle H1\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk> = UoracleH\<guillemotright>\<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>"
    apply (atomize_elim, rule exI)
    apply (subst lift_extendL[symmetric, where Q="\<lbrakk>Hin1, Hout1, Gin1, Gout1\<rbrakk>"], simp)
    apply (subst lift_extendL[symmetric, where Q="\<lbrakk>Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>"], simp)
    apply (subst assoc_op_lift'[where Q="\<lbrakk>Hin1\<rbrakk>"])
    apply (subst assoc_op_lift'[where Q="\<lbrakk>Hin2\<rbrakk>"])
    apply (subst lift_extendR[symmetric, where Q="\<lbrakk>Hin1, Hout1\<rbrakk>"], simp)
    apply (subst lift_extendR[symmetric, where Q="\<lbrakk>Hin2, Hout2\<rbrakk>"], simp)
    by simp
  have UoracleH_sa[simp]: "UoracleH* = UoracleH"
    apply (subst lift_eqOp[symmetric, where Q="\<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk>"])
    by (simp_all add: UoracleH1[symmetric] adjoint_lift[symmetric])
  have unitary_UoracleH[simp]: "unitary UoracleH"
    unfolding unitary_def apply simp
    apply (subst lift_eqOp[symmetric, where Q="\<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk>"], simp)
    by (simp flip: lift_timesOp UoracleH1, simp)
  have move_Cla_up: "unitary A \<Longrightarrow> A \<cdot> (Cla[X] \<sqinter> S) = Cla[X] \<sqinter> (A \<cdot> S)" for A X S
    by simp

  have conj_True: "(True \<and> True) = True" by simp

  have Cla_True': "x = True \<Longrightarrow> Cla[x] = top" for x by simp

  define comm1 UG2 UHq2
    where "comm1 = comm_op\<guillemotright>\<lbrakk>Hin2, Gin2\<rbrakk>"
      (* and "comm2 = comm_op\<guillemotright>\<lbrakk>Gout2, Gout2\<rbrakk>" *)
      and "UG2 = Uoracle G2\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk>"
      and "UHq2 = Uoracle (\<lambda>(m, g). mk_Hq' Hq2 H02 g pk2 m)\<guillemotright>variable_concat \<lbrakk>Gin2, Gout2\<rbrakk> \<lbrakk>Hout2\<rbrakk>"
  (* Simplifier should be able to do this automatically, but runs too long *)
  have post: "?post = 
    ((comm1 \<cdot> UG2 \<cdot> UHq2 \<cdot> UG2 \<cdot> comm1)* \<cdot> (qeq))" (is "_ = (applyOpSpace (?op* ) _)")
    unfolding comm1_def UG2_def UHq2_def
    apply (subst Cla_True', simp add: True)+
    apply (simp only: inf_top_left inf_top_right)
    apply (subst unitary_image, simp)+
    apply (simp only: inf_top_left inf_top_right)
    apply (simp only: adjoint_lift adj_comm_op Uoracle_selfadjoint times_adjoint)
    apply (simp only: timesOp_assoc_linear_space[symmetric] timesOp_assoc[symmetric])
    by (simp only: qeq_def)

  have move: "S \<le> U* \<cdot> T" if "U \<cdot> S \<le> T" and [simp]: "unitary U" for T :: "'z subspace" and U and S :: "'y subspace"
    using applyOpSpace_mono[OF that(1), where A="U*"]
    by (simp flip: timesOp_assoc_linear_space)

  let ?h2 = "Uoracle H1\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk>"

  define Q where "Q = \<lbrakk>quantA1, quantA2, Hin1, Hout1, Gin1, Gout1, Hin2, Hout2, Gin2, Gout2, tmp_Gin2, tmp_Gout2\<rbrakk>"
  have distinct_Q: "distinct_qvars Q"
    unfolding Q_def by simp
  have pred_local: "predicate_local ((h1 \<cdot> qeq) \<sqinter> ket0) Q" 
    unfolding qeq_def ket0_def Q_def h1_def by auto
  have op_local: "operator_local (comm1 \<cdot> UG2 \<cdot> UHq2 \<cdot> UG2 \<cdot> comm1) Q" 
    unfolding Q_def comm1_def UG2_def UHq2_def by auto
  have h1_local: "operator_local (Uoracle H1\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk>) Q"
    unfolding Q_def by auto

  let ?basis = "{ket (a1,a2,hin1,hout1,gin1,gout1,hin2,hout2,gin2,0,qh_gin2,qh_gout2) | a1 a2 hin1 hout1 gin1 gout1 hin2 hout2 gin2 qh_gin2 qh_gout2. True}"
  have span_basis: "liftSpace (Span ?basis) Q = ket0"
  proof -
    have 1: "Span ?basis 
      = Span (range ket) \<otimes> Span (range ket) \<otimes> Span (range ket) \<otimes> Span (range ket) \<comment> \<open>a1,a2,hin1,hout1\<close>
       \<otimes> Span (range ket) \<otimes> Span (range ket) \<otimes> Span (range ket) \<otimes> Span (range ket) \<comment> \<open>gin1,gout1,hin2,hout2\<close>
       \<otimes> Span (range ket) \<otimes> Span {ket 0} \<otimes> Span (range ket) \<otimes> Span (range ket)"
      unfolding span_tensor
      apply (auto simp: ket_product image_def simp flip: ex_simps(2))
      by meson
    have 2: "\<dots> \<guillemotright> Q = ket0"
      unfolding ket0_def Q_def
      by (auto simp: tensor_lift)
    show ?thesis 
      unfolding 1 2 by simp
  qed

  have eq: "applyOp ?op (lift_vector x Q \<psi>') = applyOp ?h2 (lift_vector x Q \<psi>')" if "x \<in> ?basis" and "\<psi>' \<in> lift_rest Q" for x \<psi>'
  proof -
    from that obtain a1 a2 hin1 hout1 gin1 gout1 hin2 hout2 gin2 qh_gin2 qh_gout2
      where x: "x = ket (a1, a2, hin1, hout1, gin1, gout1, hin2, hout2, gin2, 0, qh_gin2, qh_gout2)"
      by auto

    have "comm1 \<cdot> lift_vector x Q \<psi>'
       = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2, hin2, 0, qh_gin2, qh_gout2)) Q \<psi>'"
      unfolding comm1_def 
      apply (rewrite at "comm_op \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      by (simp add: x applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)

    also have "UG2 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2, hin2, G2 hin2, qh_gin2, qh_gout2)) Q \<psi>'"
      unfolding UG2_def 
      apply (rewrite at "Uoracle _ \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      apply (simp add: applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)
      by -

    also have "UHq2 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + mk_Hq' Hq2 H02 (G2 hin2) pk2 hin2, hin2, G2 hin2, qh_gin2, qh_gout2)) Q \<psi>'"
    (* also have "UHq2 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + mk_Hq' Hq2 H02 (G2 hin2) pk2 hin2, hin2, G2 hin2, gout2)) Q \<psi>'" *)
      unfolding UHq2_def 
      apply (rewrite at "Uoracle _ \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      apply (simp add: applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)
      apply (simp flip: ket_product)
      apply (simp add: encrT_def applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)
      by -

    also have "\<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + H1 hin2, hin2, G2 hin2, qh_gin2, qh_gout2)) Q \<psi>'"
    (* also have "\<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + H1 hin2, hin2, G2 hin2, gout2)) Q \<psi>'" *)
      by (simp add: True mk_Hq_def mk_Hq'_def encrT_def msg_spaceT_def)

    also have "UG2 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + H1 hin2, hin2, 0, qh_gin2, qh_gout2)) Q \<psi>'"
    (* also have "UG2 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, gin2, hout2 + H1 hin2, hin2, 0, gout2)) Q \<psi>'" *)
      unfolding UG2_def 
      apply (rewrite at "Uoracle _ \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      apply (simp add: applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)
      by -

    also have "comm1 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, hin2, hout2 + H1 hin2, gin2, 0, qh_gin2, qh_gout2)) Q \<psi>'"
    (* also have "comm1 \<cdot> \<dots> = lift_vector (ket (a1, a2, hin1, hout1, gin1, gout1, hin2, hout2 + H1 hin2, gin2, gout2, 0)) Q \<psi>'" *)
      unfolding comm1_def 
      apply (rewrite at "comm_op \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      by (simp add: applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)

    also have "\<dots> = Uoracle H1\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk> \<cdot> lift_vector x Q \<psi>'"
      apply (rewrite at "Uoracle _ \<guillemotright> _" reorder_variables_hint_def[symmetric, where R="Q"])
      unfolding Q_def
      using [[simp_depth_limit=80]] apply simp
      apply (simp add: x applyOp_lift times_applyOp ket_product tensorOp_applyOp_distr)
      by -

    finally show ?thesis
      by (simp add: times_applyOp)
  qed

  have "?op \<cdot> (applyOpSpace h1 qeq \<sqinter> ket0) = ?h2 \<cdot> (applyOpSpace h1 qeq \<sqinter> ket0)"
    using distinct_Q pred_local op_local h1_local 
    apply (rule applyOpSpace_eq'[where Q=Q and G="?basis"])
     apply (rule eq)
      apply simp
     apply simp
    by (subst span_basis, simp)

  also have "\<dots> \<le> qeq"
    unfolding h1_def ket0_def qeq_def
    unfolding  UoracleH1 UoracleH2 
    by (simp del: UoracleH_sa)
  finally have "?op \<cdot> (applyOpSpace h1 qeq \<sqinter> ket0) \<le> qeq"
    by assumption
  then have "applyOpSpace h1 qeq \<sqinter> ket0 \<le> ?op* \<cdot> qeq"
    apply (rule move) by (simp add: comm1_def UG2_def UHq2_def)
  then show ?thesis
    apply (subst post) 
    apply (subst eqTrueI[OF True])
    by (simp only: classical_true inf_top_left h1_def ket0_def qeq_def)
next
  case False
  show ?thesis
    apply (simp only: False classical_false inf_bot_left)
    by simp
qed

*)

end
