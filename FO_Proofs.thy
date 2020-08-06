theory FO_Proofs
  imports FO_Specification General_Proofs T_Proofs FO_Proofs0 T_Security
    (* "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools" *)
begin

(* Can be used with "simp split!:" or with Splitter.split_asm_tac *)
lemma Cla_split_asm: "P (Cla[Q]) = (\<not> ((Q \<and> \<not> P top) \<or> (\<not> Q \<and> \<not> P bot)))"
  by (cases Q, auto) 

lemma correctness_enc_leq1[simp]: 
  "correctness params keygen enc dec msg_space \<le> 1"
  apply (rule correctness_leq1)
  by auto

lemma correctness_enc_pos[simp]: 
  "correctness params keygen enc dec msg_space \<ge> 0"
  apply (rule correctness_pos)
  by auto



(* lemma case_option_beta: "x\<noteq>None \<Longrightarrow> (case x of None \<Rightarrow> y | Some z \<Rightarrow> w z) = w (the x)" *)
  (* by auto *)


lemma decapsQuery_decapsQueryPRF_vc:
"\<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> K'1 = K'2 \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk> \<le> (\<CC>\<ll>\<aa>[c2 \<noteq> cstar2] + (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = None \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = None \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)) \<sqinter> (\<CC>\<ll>\<aa>[c2 = cstar2] + (\<CC>\<ll>\<aa>[\<not> (dec () sk2 c2 = None \<or> encr () pk2 (the (dec () sk2 c2)) (G2 (the (dec () sk2 c2))) \<noteq> c2)] + (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = Some (PRF prfk2 c2) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = Some (PRF prfk2 c2) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)) \<sqinter> (\<CC>\<ll>\<aa>[dec () sk2 c2 = None \<or> encr () pk2 (the (dec () sk2 c2)) (G2 (the (dec () sk2 c2))) \<noteq> c2] + (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = Some (H2 (the (dec () sk2 c2))) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] + \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = Some (H2 (the (dec () sk2 c2))) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)))"
(* "\<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> K'1 = K'2 \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk> \<le> (\<CC>\<ll>\<aa>[c2 \<noteq> cstar2] \<squnion> (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = None \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = None \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)) \<sqinter> (\<CC>\<ll>\<aa>[c2 = cstar2] \<squnion> (\<CC>\<ll>\<aa>[\<not> (dec () sk2 c2 = None \<or> encr () pk2 (the (dec () sk2 c2)) (G2 (the (dec () sk2 c2))) \<noteq> c2)] \<squnion> (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = Some (PRF prfk2 c2) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = Some (PRF prfk2 c2) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)) \<sqinter> (\<CC>\<ll>\<aa>[dec () sk2 c2 = None \<or> encr () pk2 (the (dec () sk2 c2)) (G2 (the (dec () sk2 c2))) \<noteq> c2] \<squnion> (\<CC>\<ll>\<aa>[c1 \<noteq> cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> None = Some (H2 (the (dec () sk2 c2))) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>) \<sqinter> (\<CC>\<ll>\<aa>[c1 = cstar1] \<squnion> \<CC>\<ll>\<aa>[pk_of_sk sk2 = pk2 \<and> skfo1 = (sk2, prfk2) \<and> cstar1 = cstar2 \<and> classA1 = classA2 \<and> c1 = c2 \<and> decapsFO (G1, H1) skfo1 c1 = Some (H2 (the (dec () sk2 c2))) \<and> b1 = b2 \<and> G1 = G2 \<and> H1 = H2 \<and> Kstar1 = Kstar2 \<and> in_pk1 = in_pk2 \<and> in_cstar1 = in_cstar2] \<sqinter> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)))" *)
proof -
  note encrT_def[simp] decapsFO_def[simp] decT_def[simp]
  obtain sk1 prfk1 where [simp]: "skfo1 = (sk1,prfk1)" apply atomize_elim by auto
  consider (ccstar) "c1=cstar1" | (decNone) "c1\<noteq>cstar1 \<and> dec () sk1 c1 = None"
    | (decM) m where "c1\<noteq>cstar1 \<and> dec () sk1 c1 = Some m"
    apply atomize_elim by auto

  then show ?thesis
  proof cases
    case ccstar
    then show ?thesis
      by simp
  next
    case decNone
    then show ?thesis    
      by auto
  next case (decM m)
    then show ?thesis
      by auto
  qed
qed

lemma [simp]: "keygenFO (G,H1) = keygenFO (G,H2)"
  unfolding keygenFO_def by simp

lemma keygenFO_keygenT: "map_distr (\<lambda>x. ((fst x, fst (snd x)), snd (snd x))) (keygenFO (G, H2)) = product_distr (keygenT G) keygenPRF"
  unfolding keygenFO_def by (auto simp: case_prod_beta)


lemma pk_of_sk_keygenFO:
  assumes "x \<in> supp (keygenFO (G1, H2))"
  shows "pk_of_sk (fst (snd x)) = fst x"
  using assms unfolding keygenFO_def  
  by (auto simp: pk_of_sk)

lemma [simp]: "uniform (msg_spaceT G1) = uniform (msg_spaceT G2)"
  unfolding msg_spaceT_def by simp

lemma [simp]: "keygenFO (G, H) = keygenFO (G1, H1)"
  unfolding keygenFO_def keygenT_def by simp

(* lemma [simp]: "map_distr (\<lambda>x. ((fst x, fst (snd x)), snd (snd x), snd x)) (keygenFO (G, H)) = bind_distr (keygenT G2) (\<lambda>z. map_distr (\<lambda>x. (z, x, snd z, x)) keygenPRF)"
  unfolding keygenFO_def keygenT_def case_prod_conv
  by (simp add: case_prod_beta bind_distr_map_distr[symmetric]) *)


lemma [simp]: "map_distr (\<lambda>x. (fst x, fst (snd x))) (keygenFO (G, H)) = keygenT G2"
  unfolding keygenFO_def keygenT_def case_prod_beta
  by simp

lemma G2G2:
  assumes [simp]: "declared_qvars \<lbrakk>Gin1,Gin2,Gout1,Gout2,quantA1,quantA2,Hin1,Hout1,Hin2,Hout2\<rbrakk>"
  shows "Uoracle H\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> \<cdot> (Uoracle H\<guillemotright>\<lbrakk>Gin1, Gout1\<rbrakk> \<cdot> 
        \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)
      = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
  (is "_ = ?Q1 \<equiv>\<qq> ?Q2")
proof -
  have 1: "Uoracle H\<guillemotright>\<lbrakk>Gin1, Gout1\<rbrakk> = (idOp \<otimes> (idOp \<otimes> (idOp \<otimes> Uoracle H)))\<guillemotright>?Q1"
    apply (subst lift_tensorOp[symmetric], simp)+ by simp
  have 2: "Uoracle H\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> = (idOp \<otimes> (idOp \<otimes> (idOp \<otimes> Uoracle H)))\<guillemotright>?Q2"
    apply (subst lift_tensorOp[symmetric], simp)+ by simp
  show ?thesis
    unfolding 1 2 by simp
qed

lemma Cla_split': 
  assumes "Q \<Longrightarrow> P top" and "\<not> Q \<longrightarrow> P bot"
  shows "P (Cla[Q])"
  using assms by (cases Q, auto) 

lemma H2H2':
  assumes [simp]: "declared_qvars \<lbrakk>Gin1,Gin2,Gout1,Gout2,quantA1,quantA2,Hin1,Hout1,Hin2,Hout2\<rbrakk>"
  shows "Uoracle H\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk> \<cdot> (Uoracle H\<guillemotright>\<lbrakk>Hin1, Hout1\<rbrakk> \<cdot> 
        \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)
      = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
  (is "_ = ?Q1 \<equiv>\<qq> ?Q2")
proof -
  have 1: "Uoracle H\<guillemotright>\<lbrakk>Hin1, Hout1\<rbrakk> = (idOp \<otimes> (assoc_op* o\<^sub>C\<^sub>L (Uoracle H \<otimes> idOp) o\<^sub>C\<^sub>L assoc_op))\<guillemotright>?Q1"
    apply (subst lift_tensorOp[symmetric], simp_all)
    apply (subst assoc_op_lift')
    by (subst lift_tensorOp[symmetric], simp_all)
  have 2: "Uoracle H\<guillemotright>\<lbrakk>Hin2, Hout2\<rbrakk> = (idOp \<otimes> (assoc_op* o\<^sub>C\<^sub>L (Uoracle H \<otimes> idOp) o\<^sub>C\<^sub>L assoc_op))\<guillemotright>?Q2"
    apply (subst lift_tensorOp[symmetric], simp_all)
    apply (subst assoc_op_lift')
    by (subst lift_tensorOp[symmetric], simp_all)
  have "(assoc_op* \<cdot> Uoracle H \<otimes> idOp \<cdot> assoc_op) \<cdot> (assoc_op* \<cdot> (Uoracle H* \<otimes> idOp \<cdot> assoc_op)) = 
        assoc_op* \<cdot> (Uoracle H \<otimes> idOp \<cdot> (assoc_op \<cdot> assoc_op*) \<cdot> Uoracle H* \<otimes> idOp) \<cdot> assoc_op"
    by (simp only: timesOp_assoc)
  also have "\<dots> = idOp"
    by simp
  finally have cancel: "(assoc_op* \<cdot> Uoracle H \<otimes> idOp \<cdot> assoc_op) \<cdot> (assoc_op* \<cdot> (Uoracle H* \<otimes> idOp \<cdot> assoc_op)) = idOp"
    by -
  show ?thesis
    unfolding 1 2 by (simp add: cancel)
qed


lemma Hq1_Hq2:
  assumes notin: "cstar2 \<notin> (encrT G2 pk2) ` msg_spaceT G2"
  assumes eq: "(\<forall>x. x \<noteq> cstar2 \<longrightarrow> Hq1 x = Hq2 x)"
  shows "mk_Hq Hq1 H0 G2 pk2 = mk_Hq Hq2 H0 G2 pk2"
proof (rule ext)
  fix m
  consider (cstar) "m \<in> msg_spaceT G2" and "encrT G2 pk2 m = cstar2" | (msgspace) "m \<in> msg_spaceT G2" and "encrT G2 pk2 m \<noteq> cstar2" | (outside) "m \<notin> msg_spaceT G2" by auto
  then show "mk_Hq Hq1 H0 G2 pk2 m = mk_Hq Hq2 H0 G2 pk2 m"
  proof cases
    case msgspace
    then have "Hq1 (encrT G2 pk2 m) = Hq2 (encrT G2 pk2 m)"
      apply (subst eq[rule_format]) by simp_all
    then show ?thesis
      unfolding mk_Hq_def by auto
  next
    case cstar
    with notin have False by auto
    then show ?thesis by simp
  next
    case outside
    then show ?thesis 
      unfolding mk_Hq_def by auto
  qed
qed

lemma map_distr_Hq_Kstar:
  "map_distr (\<lambda>HK::(ciph\<Rightarrow>key)*key. ((fst HK)(cstar1 := snd HK), snd HK)) (uniform UNIV) = map_distr (\<lambda>H. (H, H cstar1)) (uniform UNIV)"
  (is "?lhs=?rhs")
proof -
  define S :: "(_ * key) set" where "S = {(H,K). H cstar1 = K}"
  have "regular_betw (\<lambda>(x,y). (x(cstar1 := y), y)) UNIV S"
  proof (rule regular_betwI)
    define n :: nat where "n=CARD(key)"
    show "n\<noteq>0" unfolding n_def by simp
    show "range (\<lambda>(x, y). (x(cstar1 := y), y)) = S"
      unfolding S_def 
      using image_iff case_prod_beta by fastforce
    show "card ((\<lambda>(x, y). (x(cstar1 := y), y)) -` {HK} \<inter> UNIV) = n" if "HK \<in> S" for HK
    proof -
      obtain H K where HK_def: "HK = (H,K)" by fastforce
      with that have H_cstar1: "H cstar1 = K" by (simp add: S_def)
      define f :: "((ciph\<Rightarrow>key)*key) \<Rightarrow> _" where "f = (\<lambda>(H',K'). H' cstar1)"
      define g :: "_ \<Rightarrow> ((ciph\<Rightarrow>key)*key)" where "g K' = (H(cstar1:=K'),K)" for K'
      show ?thesis
        unfolding n_def HK_def apply simp
      proof (rule card_bij_eq[where f=f and g=g])
        show "inj_on f ((\<lambda>(x, y). (x(cstar1 := y), y)) -` {(H, K)})"
          apply (rule inj_onI) unfolding f_def apply auto
          by (metis array_rules(5) fun_upd_triv)
        show "inj g"
          apply (rule injI) unfolding g_def apply auto
          by (meson fun_upd_eqD)
        show "range g \<subseteq> (\<lambda>(x, y). (x(cstar1 := y), y)) -` {(H, K)}"
          apply (auto simp: g_def case_prod_beta)
          using H_cstar1 by blast
      qed auto
    qed
  qed
  then have 1: "?lhs = uniform S"
    unfolding case_prod_beta by simp
  have "bij_betw (\<lambda>d. (d, d cstar1)) UNIV S"
    apply (rule bij_betwI')
    by (auto simp: S_def)
  then have 2: "?rhs = uniform S"
    by simp
  from 1 2 show ?thesis by simp
qed
















(* lemma [simp]: "weight (keygenT p) = 1"
  unfolding keygenT_def keygen_def by simp *)

lemma [simp]: "weight (keygenFO p) = 1"
  unfolding keygenFO_def case_prod_beta by auto


lemma [simp]: "weight (fakeenc () pk) = 1"
  unfolding fakeenc_def enc0_def by simp

(* 
lemma
  quantum_eq_add_state2: 
  fixes U :: "('a::universe,'c) l2bounded" and V :: "('b::universe,'c) l2bounded" and \<psi> :: "'d::universe ell2"
    and Q :: "'a::universe variables"    and R :: "'b::universe variables"    and T :: "'d variables"
  assumes "distinct_qvars (variable_concat Q (variable_concat R T))"
  assumes "norm \<psi> = 1"
  shows "quantum_equality_full V R U Q \<sqinter> Span {\<psi>}\<guillemotright>T
             = quantum_equality_full (addState \<psi> \<cdot> V) R (U \<otimes> idOp) (variable_concat Q T)"
proof -
  from assms(1) have [simp]: "distinct_qvars (variable_concat T Q)"
    by (subst (asm) distinct_qvars_split2, simp)
  then have [simp]: "distinct_qvars (variable_concat Q T)"
    by (rule distinct_qvars_swap)
  from assms(1) have [simp]: "distinct_qvars (variable_concat R Q)"
    by (subst (asm) distinct_qvars_split2, simp)
  then have [simp]: "distinct_qvars (variable_concat Q R)"
    by (rule distinct_qvars_swap)
  from assms(1) have [simp]: "distinct_qvars (variable_concat R T)"
    by (subst (asm) distinct_qvars_split2, simp)
  then have [simp]: "distinct_qvars (variable_concat T R)"
    by (rule distinct_qvars_swap)
  have [simp]: "distinct_qvars (variable_concat (variable_concat Q T) R)"
    by (subst distinct_qvars_split1, simp)
  show ?thesis
    apply (subst quantum_equality_sym, simp)
    apply (subst quantum_eq_add_state)
      apply (simp_all add: assms)[2]
    by (rule quantum_equality_sym, simp)
qed
*)

(* lemma [simp]: "paramsT \<noteq> 0"
  by (metis UNIV_not_empty finite paramsT_def suppP_empty_simp supp_uniform) *)

lemma [simp]: "disjointnessT \<le> 1"
  unfolding disjointnessT_def
  apply (rule disjointness_leq1)
  by auto

lemma [simp]: "disjointnessT \<ge> 0"
  unfolding disjointnessT_def
  apply (rule disjointness_geq0)
  by auto

lemma Prob_leq_disjointnessT: 
  assumes "G1 \<in> supp paramsT" and "(pk1, sk1) \<in> supp (keygenT G1)"
  shows "Prob (fakeenc () pk1) (encrT G1 pk1 ` msg_spaceT G1) \<le> disjointnessT"
  unfolding disjointnessT_def fakeencT_def[symmetric, of G1] encT_def
  using _ assms apply (rule disjointness_geqI[where p=G1 and pk=pk1])
  apply (metis assms(2) keygenT_def mem_simps(2) suppP_empty_simp)
  by (simp add: UNION_singleton_eq_range fakeencT_def)

(* lemma aux_xa_x_1: "(\<forall>x xa::bit. xa = x + 1 \<or> P xa x) = (\<forall>x. P x x)"
  using bit_neq by blast *)

lemma encT_injective:  
  assumes "P \<in> supp paramsT"
  assumes "(pk,sk) \<in> supp (keygenT P)"
  shows "inj_on (encrT P pk) (msg_spaceT P)"
proof -
  have "(pk,sk) \<in> supp (keygen0 ())"
    using assms(2) unfolding keygenT_def keygen_def by simp
  then have iep: "injective_enc_pk () enc0 msg_space0 pk"
    using enc0_injective[unfolded injective_enc_def, rule_format]
    by auto

  show ?thesis
  proof (rule inj_onI)
    fix m0 :: msg
      and m1 :: msg
    assume m0: "m0 \<in> msg_spaceT P"
      and m1: "m1 \<in> msg_spaceT P"
      and eqT: "encrT P pk m0 = encrT P pk m1"
    have disj: "disjnt (supp (enc0 () pk m0)) (supp (enc0 () pk m1))"
      apply (rule iep[unfolded injective_enc_pk_def, rule_format])
      using m0 m1 msg_space unfolding msg_spaceT_def by auto
    moreover have "encrT P pk m0 \<in> supp (enc0 () pk m0)"
      unfolding encrT_def encr_def enc0_def by auto
    moreover have "encrT P pk m1 \<in> supp (enc0 () pk m1)"
      unfolding encrT_def encr_def enc0_def by auto
    ultimately show "m0 = m1"
      using eqT by (auto simp: disjnt_def)
  qed
qed

lemma mk_Hq_uniform: 
  assumes "(pk,(sk,prfk)) \<in> supp (keygenFO (G,anyH))"
  shows "map_distr (\<lambda>HqH0. mk_Hq (snd HqH0) (fst HqH0) G pk) (uniform UNIV) = uniform UNIV"
    (is "?lhs = ?rhs")
proof -
  have inj_encrT: "inj_on (encrT G pk) (msg_spaceT G)"
    apply (rule encT_injective)
    using assms by (auto simp: keygenFO_def paramsT_def)
  have "?lhs = map_distr (\<lambda>HqH0' m. HqH0' (if m \<in> msg_spaceT G then Inr (encrT G pk m) else Inl m))
        (map_distr (\<lambda>HqH0 m. case m of Inl m' \<Rightarrow> fst HqH0 m' | Inr m' \<Rightarrow> snd HqH0 m') (uniform UNIV))"
    apply (simp add: mk_Hq_def[abs_def])
    apply (subst if_distrib[where f="\<lambda>x. case x of Inl x \<Rightarrow> _ x | Inr x \<Rightarrow> _ x"])
    apply (subst sum.case)+
    by auto
  also have "\<dots> = map_distr (\<lambda>HqH0' m. HqH0' (if m \<in> msg_spaceT G then Inr (encrT G pk m) else Inl m)) (uniform UNIV)"
    apply (subst map_distr_uniform[where B=UNIV])
    apply (rule bijI')
    apply auto
    apply (metis case_sum_o_inj(1))
    apply (metis case_sum_o_inj(2))
    by (metis case_sum_expand_Inr_pointfree)
  also have "\<dots> = uniform UNIV"
    apply (rule map_distr_uniform_regular[where B=UNIV])
    thm reindex_regular[where i = "\<lambda>m. (if m \<in> msg_spaceT G then Inr (encrT G pk m) else Inl m)"]
    apply (rule reindex_regular)
    apply (rule injI)
    apply (case_tac "x \<in> msg_spaceT G"; case_tac "y \<in> msg_spaceT G")
    using inj_encrT by (auto simp: inj_onD)
  finally show ?thesis
    by -
qed

lemma keygenFO_anyH: "NO_MATCH undefined H \<Longrightarrow> keygenFO (G,H) = keygenFO (G,undefined)"
  unfolding keygenFO_def by simp

lemma keygenFO_anyG: "NO_MATCH undefined G \<Longrightarrow> keygenFO (G,H) = keygenFO (undefined,H)"
  unfolding keygenFO_def keygenT_def by simp

definition "Rbad pk sk m = 
  (if m\<in>msg_space() then {r. dec () sk (encr () pk m r) \<noteq> Some m} else {})"
definition "bad_pk pk sk = (\<exists>m\<in>msg_space(). Rbad pk sk m = UNIV)"
definition "RgoodG pk sk G \<longleftrightarrow> (\<forall>m. G m \<notin> Rbad pk sk m)"

definition "\<delta>bad pk sk m = real (card (Rbad pk sk m)) / real (card (UNIV::rand set))"

lemma [simp]: "\<delta>bad pk sk m \<ge> 0"
  unfolding \<delta>bad_def by auto

lemma [simp]: "\<delta>bad pk sk m \<le> 1"
  unfolding \<delta>bad_def
  by (simp add: card_mono)

lemma \<delta>bad_correctness_pkskm: "\<delta>bad pk sk m = correctness_pkskm enc dec () pk sk m"
  if "m \<in> msg_space()"
proof -
  have "correctness_pkskm enc dec () pk sk m = Prob (uniform UNIV) (encr () pk m -` {c. dec () sk c \<noteq> Some m})"
    unfolding correctness_pkskm_def enc_def Prob_map_distr' by simp
  also have "\<dots> = real (card {r. dec () sk (encr () pk m r) \<noteq> Some m}) / real CARD(rand)"
    unfolding Prob_uniform by simp
  also have "\<dots> = \<delta>bad pk sk m"
    by (simp add: \<delta>bad_def Rbad_def that)
  finally show ?thesis
    by simp
qed

lemma \<delta>bad_correctness_pksk:
  "\<delta>bad pk sk m \<le> correctness_pksk enc dec msg_space () pk sk"
proof (cases "m \<in> msg_space()")
  case True
  then show ?thesis
    unfolding correctness_pksk_def 
    by (simp add: cSUP_upper \<delta>bad_correctness_pkskm)
next
  case False
  then show ?thesis 
    unfolding \<delta>bad_def Rbad_def by auto
qed

definition "Rbad_select pk sk = 
   map_distr (\<lambda>F. {m. F m = 1}) (product_distr' (\<lambda>m. bernoulli (\<delta>bad pk sk m)))"

lemma [simp]: "weight (Rbad_select a b) = 1"
  unfolding Rbad_select_def apply simp
  apply (rule total_product_distr'I)
  by simp

(* Needed to avoid undesired corner cases where we uniformly pick from the empty set *)
definition "Rbad' pk sk m = (if Rbad pk sk m = {} then {undefined} else Rbad pk sk m)"
definition "Rgood' pk sk m = (if Rbad pk sk m = UNIV then {undefined} else - Rbad pk sk m)"
definition "Rgood'G pk sk G \<longleftrightarrow> (\<forall>m. G m \<in> Rgood' pk sk m)"

lemma Rgood'_notempty[simp]: "Rgood' pk sk m \<noteq> {}"
  unfolding Rgood'_def (* apply (cases "Rbad pk sk m = {}") *) by auto
lemma Rbad'_notempty[simp]: "Rbad' pk sk m \<noteq> {}"
  unfolding Rbad'_def (* apply (cases "Rbad pk sk m = {}") *) by auto

lemma Rgood'_ex: "\<exists>x. \<forall>m. x m \<in> Rgood' pk sk m"
  apply (subst choice_iff[symmetric])
  using Rgood'_notempty by (meson equals0I)
lemma Rbad'_ex: "\<exists>x. \<forall>m. x m \<in> Rbad' pk sk m"
  apply (subst choice_iff[symmetric])
  using Rbad'_notempty by (meson equals0I)

(* Need to use uniform' instead of uniform in case Rbad is empty or UNIV *)
definition "G_goodbad_squash pk sk =
  bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' pk sk m})
   (\<lambda>Ggood. map_distr (Pair Ggood) 
        (bind_distr (uniform {G. \<forall>m. G m \<in> Rbad' pk sk m}) 
        (\<lambda>Gbad. map_distr (\<lambda>S. (Gbad, S, \<lambda>m. if m \<in> S then Gbad m else Ggood m)) 
              (Rbad_select pk sk))))"

lemma G_goodbad_squash_4th: "map_distr (\<lambda>x. snd (snd (snd x))) (G_goodbad_squash pk2 sk2) = uniform UNIV"
  (is "?lhs = _")
proof -
  define good bad Ber where "good = Rgood' pk2 sk2"
    and "bad = Rbad' pk2 sk2" and "Ber i = bernoulli (\<delta>bad pk2 sk2 i)" for i
  have [simp]: "bad m \<noteq> {}" and [simp]: "good m \<noteq> {}" for m
    unfolding bad_def Rbad'_def good_def Rgood'_def by auto
  have "?lhs = bind_distr (uniform {G. \<forall>m. G m \<in> good m})
     (\<lambda>goodG. bind_distr (uniform {G. \<forall>m. G m \<in> bad m})
            (\<lambda>badG. map_distr (\<lambda>c m. if m \<in> c then badG m else goodG m)
                  (Rbad_select pk2 sk2)))"
    unfolding G_goodbad_squash_def good_def bad_def 
    by (simp add: map_product_distr' flip: bind_distr_map_distr)
  also have "\<dots> = product_distr'
     (\<lambda>m. bind_distr (uniform (good m))
            (\<lambda>Ggood. bind_distr (uniform (bad m))
                   (\<lambda>Gbad. map_distr (\<lambda>c. if c = 1 then Gbad else Ggood)
                           (Ber m))))"
    (is "_ = product_distr' ?U")
    unfolding Rbad_select_def Ber_def
    apply (simp flip: product_distr'_uniform bind_distr_map_distr)
    apply (subst map_product_distr')
    apply (subst bind_product_distr')
    apply (subst bind_product_distr')
    by simp
  also { fix m
    consider (allGood) "Rbad pk2 sk2 m = {}"| (allBad) "Rbad pk2 sk2 m = UNIV"
      | (normal) "Rbad pk2 sk2 m \<noteq> {}" and "Rbad pk2 sk2 m \<noteq> UNIV" by auto
    then have "?U m = uniform UNIV"
    proof cases
      case normal
      then show ?thesis 
        unfolding Ber_def apply (subst bernoulli_combine_uniform)
        by (auto simp: \<delta>bad_def bad_def good_def disjnt_iff Rbad'_def Rgood'_def)
    next
      case allGood
      then have "\<delta>bad pk2 sk2 m = 0"
        unfolding \<delta>bad_def by simp
      then have [simp]: "Ber m = point_distr 0"
        unfolding Ber_def by (simp add: bernoulli_p0)
      from allGood have [simp]: "good m = UNIV"
        unfolding good_def Rgood'_def by simp
      show ?thesis 
        apply (subst bind_point_distr[symmetric])
        apply (subst bind_distr_twice_indep[where A="Ber m", symmetric])
        apply (subst bind_distr_twice_indep[where A="Ber m", symmetric])
        by simp
    next
      case allBad
      then have "\<delta>bad pk2 sk2 m = 1"
        unfolding \<delta>bad_def by simp
      then have [simp]: "Ber m = point_distr 1"
        unfolding Ber_def by (simp add: bernoulli_p1)
      from allBad have [simp]: "bad m = UNIV"
        unfolding bad_def Rbad'_def by simp
      show ?thesis 
        apply (subst bind_point_distr[symmetric])
        apply (subst bind_distr_twice_indep[where A="Ber m", symmetric])
        apply (subst bind_distr_twice_indep[where A="Ber m", symmetric])
        by simp
    qed
  }
  then have "product_distr' ?U = uniform UNIV"
    by auto
  finally show ?thesis by -
qed

(* Ggood,Gbad,S,G <$ G_goodbad_squash pk sk; *)
(* Must be defined exactly like the term resulting from the squash tacting 
in indcca-enc-fo-game1-game2.qrhl because it is used via "simp * G_goodbad_o2h_squash[symmetric]" *)
definition "G_goodbad_o2h_squash = 
bind_distr (keygenT undefined) (\<lambda>z. map_distr (Pair z) 
(bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' (fst z) (snd z) m})
(\<lambda>za. map_distr (Pair za) (bind_distr 
(uniform {G. \<forall>m. G m \<in> Rbad' (fst z) (snd z) m})
(\<lambda>zb. map_distr (\<lambda>x. (zb, x, \<lambda>m. if m \<in> x then zb m else za m))
(Rbad_select (fst z) (snd z)))))))"

lemma [simp]: "weight G_goodbad_o2h_squash = 1"
  unfolding G_goodbad_o2h_squash_def
  apply (simp flip: not_ex not_all)
  apply (subst choice_iff[symmetric])+
  apply (subst ex_in_conv[])+
  using Rgood'_notempty Rbad'_notempty
  by simp

(* A coupling of goodbad_o2h_distr and G_goodbad_o2h_squash.
   Returns ((pk,sk),Ggood,Gbad,S,G), (S,G,Ggood,(pk,sk)) *)
definition "goodbad_o2h_distr_ext = 
  bind_distr (keygenT undefined) (\<lambda>(pk,sk).
  bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' pk sk m}) (\<lambda>Ggood.
  bind_distr (uniform {G. \<forall>m. G m \<in> Rbad' pk sk m}) (\<lambda>Gbad.
  bind_distr (Rbad_select pk sk) (\<lambda>S::msg set.
  let G = \<lambda>m. if m \<in> S then Gbad m else Ggood m in
  point_distr (((pk,sk),Ggood,Gbad,S,G), (S,Ggood,G,(pk,sk)))))))"

lemma [simp]: "weight goodbad_o2h_distr_ext = 1"
  unfolding goodbad_o2h_distr_ext_def
  apply (simp flip: not_ex not_all add: Let_def case_prod_beta)
  apply (subst choice_iff[symmetric])+
  apply (subst ex_in_conv[])+
  using Rgood'_notempty Rbad'_notempty
  by simp

(* (S,G,G',z') <$ goodbad_o2h_distr; *)
definition "goodbad_o2h_distr =
  map_distr snd goodbad_o2h_distr_ext"

lemma weight_goodbad_o2h_distr[simp]: "weight goodbad_o2h_distr = 1"
  unfolding goodbad_o2h_distr_def by simp

lemma [simp]: "goodbad_o2h_distr \<noteq> 0"
  using weight_goodbad_o2h_distr by fastforce 

lemma goodbad_o2h_distr_oradiff:
  assumes "(S, G, H, z) \<in> supp goodbad_o2h_distr"
  assumes "x \<notin> S"
  shows "G x = H x"
  using assms unfolding goodbad_o2h_distr_def goodbad_o2h_distr_ext_def
  by (auto simp add: Let_def)

lemma [simp]: "map_distr fst goodbad_o2h_distr_ext = G_goodbad_o2h_squash"
  by (simp add: goodbad_o2h_distr_ext_def G_goodbad_o2h_squash_def
    bind_distr_map_distr[symmetric] case_prod_beta Let_def)

lemma [simp]: "map_distr snd goodbad_o2h_distr_ext = goodbad_o2h_distr"
  unfolding goodbad_o2h_distr_def by simp

lemma goodbad_o2h_distr_ext_relationships[simplified Ball_def case_prod_beta prod_eq_iff fst_conv snd_conv, rule_format]:
  "\<forall>(((pk1,sk1),Ggood1,Gbad1,S1,G1), (S2,G2,G'2,z'2))\<in>supp goodbad_o2h_distr_ext. 
  (pk1,sk1) = z'2 \<and> G1=G'2 \<and> S1=S2"  
  unfolding goodbad_o2h_distr_ext_def
  by (simp add: case_prod_beta Let_def)

(* (S,G,z) <$ goodbad_scs_distr; *)
definition "goodbad_scs_distr = 
  bind_distr (keygenT undefined) (\<lambda>(pk,sk).
  bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' pk sk m}) (\<lambda>Ggood.
  bind_distr (Rbad_select pk sk) (\<lambda>S::msg set.
  point_distr (S,Ggood,(pk,sk)))))"

lemma [simp]: "weight goodbad_scs_distr = 1"
  unfolding goodbad_scs_distr_def 
  apply (simp flip: not_ex not_all add: Let_def case_prod_beta)
  apply (subst choice_iff[symmetric])+
  apply (subst ex_in_conv[])+
  using Rgood'_notempty Rbad'_notempty
  by simp

lemma map_distr_goodbad_o2h_distr_goodbad_scs_distr:
  "map_distr (\<lambda>x. (fst x, fst (snd x), snd (snd (snd x)))) goodbad_o2h_distr = goodbad_scs_distr"
proof -
  have "map_distr (\<lambda>(S,G,G',z'). (S,G,z')) goodbad_o2h_distr = goodbad_scs_distr"
    unfolding goodbad_o2h_distr_def goodbad_o2h_distr_ext_def goodbad_scs_distr_def
    apply (simp flip: bind_distr_map_distr add: case_prod_beta Let_def)
  apply (subst choice_iff[symmetric])+
  apply (subst ex_in_conv[])+
  using Rbad'_notempty unfolding case_prod_beta by simp
  then show ?thesis
    unfolding case_prod_beta by -
qed

lemma squash_rnd1:
  "map_distr (\<lambda>x. (snd (snd x), fst (snd x), fst x)) goodbad_scs_distr = bind_distr (keygenT undefined) (\<lambda>z. map_distr (Pair z) (product_distr (uniform {G. \<forall>m. G m \<in> Rgood' (fst z) (snd z) m}) (Rbad_select (fst z) (snd z))))"
  unfolding goodbad_scs_distr_def
  by (simp flip: bind_distr_map_distr add: case_prod_beta)




lemma comm_op_Gout2_tmp_Gout2:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gout2\<rbrakk>"
  shows "(comm_op\<guillemotright>\<lbrakk>Gout2, tmp_Gout2\<rbrakk>) \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>
        = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2\<rbrakk>"
    (is "?lhs = ?rhs")
proof -
  define C where "C = comm_op\<guillemotright>\<lbrakk>Gout2, tmp_Gout2\<rbrakk>"
  have "unitary C"
    unfolding C_def by simp
  note colo = qvar_trafo'_colocal[OF _ \<open>unitary C\<close>]
  have C_tmp_Gout2: "qvar_trafo' C \<lbrakk>tmp_Gout2\<rbrakk> \<lbrakk>Gout2\<rbrakk>"
     unfolding C_def by (rule qvar_trafo'_comm_op', simp)
  have C1: "qvar_trafo' C \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk>"
    by (rule colo, simp add: C_def)
  have C2:"qvar_trafo' C \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    by (fact C_tmp_Gout2)
  from C1 C2 have "qvar_trafo' C
     (variable_concat \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2\<rbrakk>)
     (variable_concat \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>)"
    by (rule qvar_trafo'_concat, simp_all)
  then show ?thesis
    unfolding C_def
    by (rule qvar_trafo'_quantum_equality_full)
qed

lemma comm_op_Gout2_tmp_Gout2_tmp:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gout2, tmp_Gout1\<rbrakk>"
  shows "(comm_op\<guillemotright>\<lbrakk>Gout2, tmp_Gout2\<rbrakk>) \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gout2\<rbrakk>
        = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2, Gout2\<rbrakk>"
    (is "?lhs = ?rhs")
proof -
  define C where "C = comm_op\<guillemotright>\<lbrakk>Gout2, tmp_Gout2\<rbrakk>"
  have "unitary C"
    unfolding C_def by simp
  note colo = qvar_trafo'_colocal[OF _ \<open>unitary C\<close>]
  have C_tmp_Gout2: "qvar_trafo' C \<lbrakk>tmp_Gout2\<rbrakk> \<lbrakk>Gout2\<rbrakk>"
     unfolding C_def by (rule qvar_trafo'_comm_op', simp)
  have C_tmp_Gout2': "qvar_trafo' C \<lbrakk>Gout2\<rbrakk> \<lbrakk>tmp_Gout2\<rbrakk>"
    unfolding C_def by (rule qvar_trafo'_comm_op, simp)
  have C1: "qvar_trafo' C \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk>"
    by (rule colo, simp add: C_def)
  have C2:"qvar_trafo' C \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2, Gout2\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gout2\<rbrakk>"
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (rule colo, simp add: C_def)
    apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
     apply (fact C_tmp_Gout2)
    by (fact C_tmp_Gout2')
  from C1 C2 have "qvar_trafo' C
     (variable_concat \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2, Gout2\<rbrakk>)
     (variable_concat \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, tmp_Gout1\<rbrakk> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gout2\<rbrakk>)"
    by (rule qvar_trafo'_concat, simp_all)
  then show ?thesis
    unfolding C_def
    by (rule qvar_trafo'_quantum_equality_full)
qed

lemma comm_op_Gout2_tmp_Gout2':
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, quantA2, Hin2, Hout2, tmp_Gin2, Gout2, tmp_Gout2\<rbrakk>"
  shows "(comm_op\<guillemotright>\<lbrakk>Gout2, tmp_Gout2\<rbrakk>) \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>
        = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, Gout2\<rbrakk>"
    (is "?lhs = ?rhs")
  apply (rule qvar_trafo'_quantum_equality_full)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_comm_op, simp)
  by -



lemma comm_op_Gin2_tmp_Gin2:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, quantA2, Hin2, Hout2, Gin2, tmp_Gout2, tmp_Gin2\<rbrakk>"
  shows "(comm_op\<guillemotright>\<lbrakk>Gin2, tmp_Gin2\<rbrakk>) \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, tmp_Gout2\<rbrakk>
       = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, tmp_Gout2\<rbrakk>"
  apply (rule qvar_trafo'_quantum_equality_full)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_comm_op', simp)
  by (rule qvar_trafo'_colocal, simp, simp)

lemma comm_op_Gin2_tmp_Gin2':
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1, quantA2, Hin2, Hout2, Gin2, Gout2, tmp_Gin2\<rbrakk>"
  shows "comm_op\<guillemotright>\<lbrakk>Gin2, tmp_Gin2\<rbrakk> \<cdot> \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, tmp_Gin2, Gout2\<rbrakk>
         = \<lbrakk>quantA1, Hin1, Hout1, Gin1, Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2, Hin2, Hout2, Gin2, Gout2\<rbrakk>"
  apply (rule qvar_trafo'_quantum_equality_full)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_colocal, simp, simp)
  apply (rule qvar_trafo'_concat[rotated 2], simp, simp)
   apply (rule qvar_trafo'_comm_op, simp)
  apply (rule qvar_trafo'_colocal, simp, simp)
  by -


lemma aux5a:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, quantA2, Gout2, Gin2, aux1, aux2\<rbrakk>"
  shows "\<lbrakk>quantA1,aux1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,aux2\<rbrakk> 
        \<sqinter> Span {ket (gin2, G2 gin2)}\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> 
    \<le> \<lbrakk>quantA1,aux1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,aux2\<rbrakk> 
      \<sqinter> Span {ket (G2 gin2)}\<guillemotright>\<lbrakk>Gout2\<rbrakk> \<squnion> (- Span {ket (G2 gin2)})\<guillemotright>\<lbrakk>Gout2\<rbrakk>"
  apply (rule sup.coboundedI1)
  apply (rule inf_mono)
   apply simp
  apply (rule ket_less_specific)
  by simp

lemma aux5b:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, quantA2, Gout2, Gin2, aux1, aux2\<rbrakk>"
  shows "x \<noteq> G2 gin2 \<Longrightarrow> \<lbrakk>quantA1,aux1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,aux2\<rbrakk> 
        \<sqinter> Span {ket (gin2, G2 gin2)}\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk> \<le> (- Span {ket x})\<guillemotright>\<lbrakk>Gout2\<rbrakk>"
  apply (rule inf.coboundedI2)
  apply (rule order_trans)
   apply (rule ket_less_specific)
   apply simp
  apply simp
  apply (rule span_ortho_span)
  by simp

(* lemma variable_for_name[intro]: "variable_name (Abs_variable (Abs_variable_raw (name,range (embedding::'a\<Rightarrow>_))) :: 'a::universe variable) = name"
  unfolding variable_name.rep_eq
  apply (subst Abs_variable_inverse)
  unfolding variable_raw_domain.rep_eq
   apply simp
  apply (subst Abs_variable_raw_inverse)
    apply simp_all
  unfolding variable_raw_name.rep_eq
  apply (subst Abs_variable_raw_inverse)
  by auto *)

lemma aux6:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1, quantA2, Gout2, Gin2, aux1, aux2\<rbrakk>"
  shows "\<lbrakk>quantA1,aux1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,aux2\<rbrakk> \<sqinter> Span {ket gin2}\<guillemotright>\<lbrakk>Gin2\<rbrakk> \<le> \<CC>\<ll>\<aa>[\<parallel>ket 0\<parallel> = 1] \<sqinter> (\<lbrakk>quantA1,aux1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,aux2\<rbrakk> \<sqinter> Span {ket (gin2, 0)}\<guillemotright>\<lbrakk>Gin2, Gout2\<rbrakk>) \<div> ket 0\<guillemotright>\<lbrakk>Gout2\<rbrakk>"
  apply (auto intro: inf.coboundedI2 inf.coboundedI1)
  apply (subst inf_commute, subst inf_assoc, rule inf.coboundedI2, subst inf_commute)
  apply (subst tensor_lift[symmetric], simp)
  apply (subst span_tensor)
  by (simp add: ket_product)

lemma [simp]: "{..<n} = {} \<longleftrightarrow> n=0" for n :: nat
  by auto

lemma correctness_pksk_enc_leq1[simp]: "correctness_pksk enc dec msg_space p pk sk \<le> 1"
  apply (rule correctness_pksk_leq1)
  by auto


lemma Prob_Rbad_select: "Prob (Rbad_select pk sk) (Collect ((\<in>) guess2)) = \<delta>bad pk sk guess2"
proof -
  have "Prob (Rbad_select pk sk) (Collect ((\<in>) guess2)) =
        prob (map_distr (\<lambda>S. guess2\<in>S) (Rbad_select pk sk)) True"
    by (subst Prob_map_distr, simp)
  also have "\<dots> = prob (bernoulli (\<delta>bad pk sk guess2)) 1"
    apply (simp add: Rbad_select_def)
    apply (subst map_distr_product_distr'_onepoint, simp)
    apply (subst prob_True_prob_1, simp)
    apply (rewrite at "map_distr \<hole>" DEADID.rel_mono_strong[of _ "\<lambda>x. x"])
    by auto
  also have "\<dots> = \<delta>bad pk sk guess2"
    apply (subst bernoulli1)
    by auto
  finally show ?thesis
    by -
qed

(* lemma "bind_distr \<mu> (\<lambda>x. bernoulli (f x)) = bernoulli (expectation (map_distr f \<mu>))" *)


lemma bind_keygen_bernoulli_correct: 
  "bind_distr (keygenT undefined) (\<lambda>x. bernoulli (correctness_pksk enc dec msg_space () (fst x) (snd x))) = bernoulli (correctness params keygen enc dec msg_space)"
proof (rule bin_distr_eqI[where x=1 and y=0], (auto)[3])
  define c C where "c x = correctness_pksk enc dec msg_space () (fst x) (snd x)" 
    and "C = correctness params keygen enc dec msg_space" for x
  have "prob (bind_distr (keygenT undefined) (\<lambda>x. bernoulli (c x))) 1 = 
       prob (bind_distr (map_distr c (keygenT undefined)) bernoulli) 1"
    apply (subst bind_distr_map_distr') by simp
  also have "\<dots> = expectation' (keygenT undefined) c"
    apply (rule prob_bind_distr_bernoulli) 
    unfolding c_def by auto
  also have "\<dots> = C"
    unfolding C_def c_def correctness_def params_def params0_def keygenT_def case_prod_beta
    by simp
  also have "\<dots> = prob (bernoulli C) 1"
    apply (subst bernoulli1)
    unfolding C_def by auto
  finally show "prob (bind_distr (keygenT undefined) (\<lambda>x. bernoulli (c x))) 1 = prob (bernoulli C) 1"
    by -
qed

lemma aux7: 
  assumes "x <= 4 * real (qG + 2 * qH + qD + 1) * y"
  shows "2 * sqrt ((1 + real (qG + 2 * qH + qD + 1)) * x)
     \<le> 2 * sqrt (4 * (1 + real (qG + 2 * qH + qD + 1)) * 
        real (qG + 2 * qH + qD + 1) * y)"
  apply (subst (5) mult.commute)
  apply (subst mult.assoc)
  using assms by auto

lemma aux8:
  assumes "x \<le> y"
  shows "4 * real (qG + 2 * qH + qD + 1) * x \<le> (4 + (4 * real qG + 8 * real qH + 4 * real qD)) * y"
  (* shows "4 * real (qG + 2 * qH + qD + 1) * x \<le> (1 + (real qG + 2 * real qH + real qD)) * y" *)
  (* shows "4 * real (qG + 2 * qH + qD + 1) * x \<le> (4 + (4 * real qG + 8 * real qH + 4 * real qD)) * y" *)
  using assms by auto

definition "G_goodbad_o2h_squash2 = 
bind_distr (keygenT undefined) (\<lambda>z. map_distr (Pair z) (bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' (fst z) (snd z) m}) (\<lambda>za. map_distr (Pair za) (bind_distr (uniform {G. \<forall>m. G m \<in> Rbad' (fst z) (snd z) m}) (\<lambda>zb. map_distr (\<lambda>x. (zb, x, za)) (Rbad_select (fst z) (snd z)))))))"

(* A coupling of goodbad_o2h_distr and G_goodbad_o2h_squash2.
   Returns ((pk,sk),Ggood,Gbad,S,G), (S,G,Ggood,(pk,sk)) *)
definition "goodbad_o2h_distr_ext2 = 
  bind_distr (keygenT undefined) (\<lambda>(pk,sk).
  bind_distr (uniform {G. \<forall>m. G m \<in> Rgood' pk sk m}) (\<lambda>Ggood.
  bind_distr (uniform {G. \<forall>m. G m \<in> Rbad' pk sk m}) (\<lambda>Gbad.
  bind_distr (Rbad_select pk sk) (\<lambda>S::msg set.
  let G = \<lambda>m. if m \<in> S then Gbad m else Ggood m in
  point_distr (((pk,sk),Ggood,Gbad,S,Ggood), (S,Ggood,G,(pk,sk)))))))"

lemma goodbad_o2h_distr_ext2_relationships[simplified Ball_def case_prod_beta prod_eq_iff fst_conv snd_conv, rule_format]:
  "\<forall>(((pk1,sk1),Ggood1,Gbad1,S1,G1), (S2,G2,G'2,z'2))\<in>supp goodbad_o2h_distr_ext2. 
  (pk1,sk1) = z'2 \<and> G1=G2 \<and> S1=S2"  
  unfolding goodbad_o2h_distr_ext2_def
  by (simp add: case_prod_beta Let_def)

lemma [simp]: "map_distr fst goodbad_o2h_distr_ext2 = G_goodbad_o2h_squash2"
  unfolding goodbad_o2h_distr_ext2_def G_goodbad_o2h_squash2_def
    Let_def bind_distr_map_distr[symmetric] case_prod_beta 
  by simp

lemma [simp]: "map_distr snd goodbad_o2h_distr_ext2 = goodbad_o2h_distr"
  unfolding goodbad_o2h_distr_def goodbad_o2h_distr_ext2_def goodbad_o2h_distr_ext_def
    Let_def bind_distr_map_distr[symmetric] case_prod_beta 
  by simp

lemma [simp]: "a \<sqinter> b \<sqinter> c \<le> b" for b :: "_::semilattice_inf"
  by (simp add: inf.coboundedI1)

lemma [simp]: "a \<sqinter> b \<sqinter> c \<le> a" for b :: "_::semilattice_inf"
  by (simp add: inf.coboundedI1)



lemma Prob_goodbad_o2h_distr_bad_pk: 
  "Prob goodbad_o2h_distr {(S, G, G', x, y). bad_pk x y} \<le> correctness params keygen enc dec msg_space"
proof -
  have [simp]: "\<exists>xa. \<forall>m. xa m \<in> Rgood' (fst x) (snd x) m" for x
    by (simp add: Rgood'_ex)
  have [simp]: "\<exists>xa. \<forall>m. xa m \<in> Rbad' (fst x) (snd x) m" for x
    by (simp add: Rbad'_ex)
  let ?cpksk = "correctness_pksk enc dec msg_space ()"
  let ?cpkskm = "correctness_pkskm enc dec ()"
  have "?cpksk pk sk \<ge> 1" if "bad_pk pk sk" for pk sk
  proof -
    from that obtain m where msg_space: "m\<in>msg_space ()" and "Rbad pk sk m = UNIV"
      unfolding bad_pk_def by auto
    then have "dec () sk (encr () pk m r) \<noteq> Some m" for r
      unfolding Rbad_def by auto
    with msg_space have "?cpkskm pk sk m = 1"
      unfolding correctness_pkskm_def enc_def Prob_map_distr by auto
    with msg_space show "?cpksk pk sk \<ge> 1"
      by (metis (full_types) \<delta>bad_correctness_pksk \<delta>bad_correctness_pkskm)
  qed
  moreover have "bad_pk pk sk" if "?cpksk pk sk \<ge> 1" for pk sk
  proof -
    from that have "?cpksk pk sk = 1"
      by (simp add: basic_trans_rules(24))
    from this[symmetric] have "1 \<in> correctness_pkskm enc dec () pk sk ` msg_space ()"
    unfolding correctness_pksk_def
    by (metis (full_types) Max_ge Max_in cSup_eq_maximum equals0D equals0I finite finite_imageI imageI nonempty_msg_space)
    then obtain m where msg_space: "m\<in>msg_space ()" and "?cpkskm pk sk m = 1"
      by auto
    then have "Prob (enc () pk m) {c. dec () sk c \<noteq> Some m} = 1"
      unfolding correctness_pkskm_def by simp
    then have "Prob (uniform UNIV) {r. dec () sk (encr () pk m r) \<noteq> Some m} = 1"
      unfolding Prob_map_distr enc_def by simp
    then have "{r. dec () sk (encr () pk m r) \<noteq> Some m} = UNIV"
      apply (rule full_Prob[rotated 2])
      by auto
    with msg_space have "Rbad pk sk m = UNIV"
      unfolding Rbad_def by simp
    with msg_space show "bad_pk pk sk"
      unfolding bad_pk_def by auto
  qed
  ultimately have bad_pk_cpksk: "bad_pk pk sk \<longleftrightarrow> ?cpksk pk sk \<ge> 1" for pk sk
    by auto

  have "Prob goodbad_o2h_distr {(S, G, G', x, y). bad_pk x y} = Prob (keygenT undefined) {(pk,sk). bad_pk pk sk}"
    unfolding goodbad_o2h_distr_def goodbad_o2h_distr_ext_def Prob_map_distr case_prod_beta bind_distr_map_distr[symmetric] Let_def
    by simp

  also have "\<dots> = Prob (map_distr (\<lambda>(pk,sk). ?cpksk pk sk) (keygenT undefined)) {1..}"
    apply (subst bad_pk_cpksk)
    unfolding bad_pk_def correctness_pksk_def Prob_map_distr case_prod_beta
    by auto

  also have "\<dots> \<le> expectation (map_distr (\<lambda>(pk,sk). ?cpksk pk sk) (keygenT undefined)) / 1"
    apply (rule markov_inequality)
    apply (rule expectation_exists_bounded[where a=0 and b=1])
    by auto
  also have "\<dots> = correctness params keygen enc dec msg_space"
    unfolding correctness_def params_def params0_def keygenT_def
    by simp
  finally show ?thesis
    by -
qed

lemma Rgood'_def':
  assumes "\<not> bad_pk pk sk"
  assumes "m \<in> msg_space()"
  shows "Rgood' pk sk m = - Rbad pk sk m"
  using assms unfolding Rgood'_def bad_pk_def by auto

lemma guard_equal_not_in_range:
  fixes pk sk G c
  assumes good: "Rgood'G pk sk G"
  defines "m' == dec () sk c"
  shows "(if bad_pk pk sk then (c \<notin> encrT G pk ` msg_space ()) 
          else (m'=None \<or> encrT G pk (the m') \<noteq> c))
       \<longleftrightarrow> c \<notin> encrT G pk ` msg_space ()"
proof (cases "bad_pk pk sk")
  case True
  then show ?thesis by simp
next
  case False
  note not_bad = False

  have "m'\<noteq>None" if "c \<in> encrT G pk ` msg_space ()"
  proof -
    from that obtain m2 where msg_space: "m2 \<in> msg_space ()" and c: "c = encrT G pk m2"
      unfolding msg_spaceT_def apply atomize_elim by auto
    from good have "G m2 \<in> Rgood' pk sk m2"
      unfolding Rgood'G_def by simp
    with not_bad msg_space have "G m2 \<notin> Rbad pk sk m2"
      apply (subst (asm) Rgood'_def')
      by auto
    with msg_space have "dec () sk c = Some m2"
      unfolding Rbad_def encrT_def c by simp
    with m'_def have "m' = Some m2"
      by simp
    then show ?thesis
      by simp
  qed

  moreover have "encrT G pk (the m') = c" if "c \<in> encrT G pk ` msg_space ()" and "m' \<noteq> None"
  proof -
    from \<open>m' \<noteq> None\<close> obtain m where m': "m' = Some m"
      by auto
    from that obtain m2 where msg_space: "m2 \<in> msg_space ()" and c: "c = encrT G pk m2"
      unfolding msg_spaceT_def apply atomize_elim by auto
    from good have "G m2 \<in> Rgood' pk sk m2"
      unfolding Rgood'G_def by simp
    with not_bad msg_space have "G m2 \<notin> Rbad pk sk m2"
      apply (subst (asm) Rgood'_def')
      by auto
    with msg_space have "dec () sk c = Some m2"
      unfolding Rbad_def encrT_def c by simp
    with m' m'_def have "m = m2"
      by simp
    with c show ?thesis
      unfolding encrT_def m' by auto
  qed

  moreover have "c \<in> encrT G pk ` msg_space ()" 
    if "m'\<noteq>None" and c_def[symmetric]: "encrT G pk (the m') = c"
  proof -
    from that obtain m where msg_space: "m \<in> msg_space ()" and m': "m' = Some m"
      \<comment> \<open>Uses that dec never returns a message outside the msg_space by construction\<close>
      apply atomize_elim unfolding dec_def m'_def apply auto
      by (smt option.case_eq_if option.sel option.simps(2))
    have "c = encrT G pk m"
      unfolding encrT_def c_def m' by simp
    with msg_space show ?thesis by auto
  qed
  ultimately show ?thesis using False by auto
qed
  
lemma goodbad_o2h_distr_goodG:
  assumes "(S, Ggood, Gbad, (pk,sk)) \<in> supp goodbad_o2h_distr"
  shows "Rgood'G pk sk Ggood"
proof -
  from assms have "Ggood \<in> supp (uniform {G. \<forall>m. G m \<in> Rgood' pk sk m})"
    unfolding goodbad_o2h_distr_def goodbad_o2h_distr_ext_def
    by (auto simp: Let_def)
  then have "Ggood m \<in> Rgood' pk sk m" for m
    apply (cases "{G. \<forall>m. G m \<in> Rgood' pk sk m} = {}")
     apply simp
    apply (subst (asm) supp_uniform)
    apply auto using Rgood'_ex by blast
  then show ?thesis
    unfolding Rgood'G_def by simp
qed


lemma dec_msg_spaceI: "Some m = dec () sk c \<Longrightarrow> m \<in> msg_space ()"
  unfolding dec_def apply (cases "dec0 () sk c") apply auto
  by (metis option.sel option.simps(2))

definition "HqHr_match pk G Hq1 Hr1 Hq2 \<longleftrightarrow> 
  (\<forall>c\<in>encrT G pk ` msg_space (). Hq1 c = Hq2 c) 
  \<and> (\<forall>c. c \<notin> encrT G pk ` msg_space () \<longrightarrow> Hr1 c = Hq2 c)"
  for Hq1 Hr1 Hq2 :: "ciph \<Rightarrow> key"

definition "HqHr_joint_pick pk G = map_distr (\<lambda>(Hq::ciph\<Rightarrow>key,Hr). ((Hq,Hr),
  ((\<lambda>c. if c \<in> encrT G pk ` msg_space() then Hq c else Hr c),
   (\<lambda>c. if c \<in> encrT G pk ` msg_space() then Hr c else Hq c))))
  (uniform UNIV)"
  

lemma HqHr_joint_pick_fst: "map_distr fst (HqHr_joint_pick pk G) = uniform UNIV"
  unfolding HqHr_joint_pick_def by (simp add: case_prod_beta)

lemma HqHr_joint_pick_snd: "map_distr snd (HqHr_joint_pick pk G) = uniform UNIV"
proof -
  define f :: \<open>(ciph\<Rightarrow>key) * (ciph\<Rightarrow>key) \<Rightarrow> (ciph\<Rightarrow>key) * (ciph\<Rightarrow>key)\<close> where "f = (\<lambda>(Hq,Hr).
        ((\<lambda>c. if c \<in> encrT G pk ` msg_space() then Hq c else Hr c),
         (\<lambda>c. if c \<in> encrT G pk ` msg_space() then Hr c else Hq c)))"
  have "f o f = id"
  proof (rule ext, case_tac x, simp)
    fix Hq Hr
    have \<open>fst (f (f (Hq,Hr))) = Hq\<close>
      unfolding f_def by auto
    moreover have \<open>snd (f (f (Hq,Hr))) = Hr\<close>
      unfolding f_def by auto
    ultimately show \<open>f (f (Hq,Hr)) = (Hq,Hr)\<close>
      by (simp add: prod_eq_iff)
  qed
  with this have "bij f"
    by (rule o_bij)
  have "map_distr snd (HqHr_joint_pick pk G) = map_distr f (uniform UNIV)"
    unfolding case_prod_beta HqHr_joint_pick_def f_def by simp
  also from \<open>bij f\<close> have "\<dots> = uniform UNIV"
    by (rule map_distr_uniform)
  finally show ?thesis
    by -
qed

lemma HqHr_joint_pick_supp: 
  assumes "((Hq1,Hr1),(Hq2,Hr2)) \<in> supp (HqHr_joint_pick pk G)"
  shows "HqHr_match pk G Hq1 Hr1 Hq2"
proof -
  have "Hq1 c = Hq2 c" if "c\<in>encrT G pk ` msg_space ()" for c
  proof -
    from assms 
    have "(Hq1,Hq2) \<in> (\<lambda>((Hq1,Hr1),(Hq2,Hr2)). (Hq1,Hq2)) ` supp (HqHr_joint_pick pk G)"
      by (metis (mono_tags, lifting) old.prod.case rev_image_eqI)
    also have "\<dots> = (\<lambda>(Hq, Hr).
           (Hq, (\<lambda>c. if c \<in> encrT G pk ` msg_space () then Hq c else Hr c))) ` UNIV"
      unfolding HqHr_joint_pick_def by (simp add: image_comp case_prod_beta)
    finally obtain Hq Hr where "Hq1 = Hq" and "Hq2 = (\<lambda>c. if c \<in> encrT G pk ` msg_space () then Hq c else Hr c)"
      apply atomize_elim by auto
    then show "Hq1 c = Hq2 c"
      using that by simp
  qed
  moreover have "Hr1 c = Hq2 c" if "c \<notin> encrT G pk ` msg_space ()" for c
  proof -
    from assms 
    have "(Hr1,Hq2) \<in> (\<lambda>((Hq1,Hr1),(Hq2,Hr2)). (Hr1,Hq2)) ` supp (HqHr_joint_pick pk G)"
      by (metis (mono_tags, lifting) old.prod.case rev_image_eqI)
    also have "\<dots> = (\<lambda>(Hq, Hr).
           (Hr, (\<lambda>c. if c \<in> encrT G pk ` msg_space () then Hq c else Hr c))) ` UNIV"
      unfolding HqHr_joint_pick_def by (simp add: image_comp case_prod_beta)
    finally obtain Hq Hr where "Hr1 = Hr" and "Hq2 = (\<lambda>c. if c \<in> encrT G pk ` msg_space () then Hq c else Hr c)"
      apply atomize_elim by auto
    then show "Hr1 c = Hq2 c"
      using that by simp
  qed
  ultimately show ?thesis
    unfolding HqHr_match_def by auto
qed

lemma HqHr_match_mk_Hq:
  assumes "HqHr_match pk G Hq1 Hr1 Hq2"
  shows "mk_Hq Hq1 H0 G pk = mk_Hq Hq2 H0 G pk"
proof (rule ext, rename_tac m, case_tac "m \<in> msg_space ()")
  fix m :: msg
  assume m: "m \<in> msg_space ()"
  then have "Hq1 (encrT G pk m) = Hq2 (encrT G pk m)"
    using assms unfolding HqHr_match_def by auto
  then show "mk_Hq Hq1 H0 G pk m = mk_Hq Hq2 H0 G pk m"
    by (simp add: mk_Hq_def m msg_spaceT_def)
next
  fix m :: msg
  assume "m \<notin> msg_space ()"
  then show "mk_Hq Hq1 H0 G pk m = mk_Hq Hq2 H0 G pk m"
    by (simp add: mk_Hq_def msg_spaceT_def)
qed

lemma reorder_qeq1:
  assumes [simp]: "declared_qvars \<lbrakk>quantA1,Gin1,Gout1,Hin1,Hout1,quantA2,Gin2,Gout2,Hin2,Hout2\<rbrakk>"
  shows "\<lbrakk>quantA1,Gin1,Gout1,Hin1,Hout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,Gin2,Gout2,Hin2,Hout2\<rbrakk>
       = \<lbrakk>quantA1,Hin1,Hout1,Gin1,Gout1\<rbrakk> \<equiv>\<qq> \<lbrakk>quantA2,Hin2,Hout2,Gin2,Gout2\<rbrakk>"
proof -
  obtain A where A1: "qvar_trafo A \<lbrakk>quantA1,Gin1,Gout1,Hin1,Hout1\<rbrakk> \<lbrakk>quantA1,Hin1,Hout1,Gin1,Gout1\<rbrakk>"
             and A2: "qvar_trafo A \<lbrakk>quantA2,Gin2,Gout2,Hin2,Hout2\<rbrakk> \<lbrakk>quantA2,Hin2,Hout2,Gin2,Gout2\<rbrakk>"
    apply atomize_elim apply (rule exI, rule conjI)

     apply (rule qvar_trafo_mult)
      apply (rule qvar_trafo_comm_op, simp)
     apply (rule qvar_trafo_mult)
      apply (rule qvar_trafo_tensor, simp)
        defer
        apply (rule qvar_trafo_mult)
         apply (rule qvar_trafo_assoc_op, simp)
        apply (rule qvar_trafo_comm_op, simp)
       apply (rule qvar_trafo_id, simp)
      apply (rule qvar_trafo_mult)
       apply (rule qvar_trafo_tensor, simp)
         defer
       apply (rule qvar_trafo_adj)
         apply (rule qvar_trafo_assoc_op, simp)
        apply (rule qvar_trafo_id, simp)
       apply (rule qvar_trafo_comm_op, simp)

    (* Witness is \<^term>\<open>(comm_op \<cdot> assoc_op* \<otimes> idOp \<cdot> (comm_op \<cdot> assoc_op) \<otimes> idOp \<cdot> comm_op)\<close> *)

     apply (rule qvar_trafo_mult)
      apply (rule qvar_trafo_comm_op, simp)
     apply (rule qvar_trafo_mult)
      apply (rule qvar_trafo_tensor, simp)
        defer
        apply (rule qvar_trafo_mult)
         apply (rule qvar_trafo_assoc_op, simp)
        apply (rule qvar_trafo_comm_op, simp)
       apply (rule qvar_trafo_id, simp)
      apply (rule qvar_trafo_mult)
       apply (rule qvar_trafo_tensor, simp)
         defer
       apply (rule qvar_trafo_adj)
         apply (rule qvar_trafo_assoc_op, simp)
        apply (rule qvar_trafo_id, simp)
       apply (rule qvar_trafo_comm_op, simp)

    by auto

  have [simp]: "(A \<cdot> A*) = idOp"
    using qvar_trafo_unitary[OF A1] by simp

  show ?thesis
    apply (subst quantum_equality_reorder[OF A1 A2])
    by auto
qed

lemma abs_compute_step:
  fixes r s x y z :: real
  assumes "abs (x - z) \<le> s"
  assumes "abs (z - y) \<le> r - s"
  shows "abs (x - y) \<le> r"
  using assms by auto

lemma abs_compute_end:
  fixes r s x y z :: real
  assumes "r \<ge> 0"
  shows "abs (x - x) \<le> r"
  using assms by auto

lemma flip_abs:
  fixes r :: real
  assumes "abs (x - y) \<le> r"
  shows "abs (y - x) \<le> r"
  using assms apply (subst abs_minus_commute) by simp

lemma ds_encT_security2_aux: 
  assumes abs1: "abs1' \<le> abs1" and abs2: "abs2' \<le> abs2"
  assumes abs2_pos: "abs2' \<ge> 0"
  assumes ds: "ds \<le> abs1' + 2 * sqrt(1+real q) * sqrt( abs2' + 4 * q / real (card (msg_space())) )"
  shows "ds \<le> abs1 + 2 * sqrt(1+q) * sqrt( abs2 + 4 * q / card (msg_space()) )"
  using ds apply (rule order.trans)
  using abs1 apply (rule add_mono)
  apply (rule mult_mono)
     apply simp
  apply (rule real_sqrt_le_mono)
  using abs2 abs2_pos by auto

lemma disjointnessT0': "disjointnessT = 0"
  apply (rule disjointnessT0)
  by (simp add: enc0_injective)

lemma security_encFO_aux:
  assumes leq1: "ds' \<le> ds0'a+ds0'b"
  assumes leq2: "ds \<le> ds0a+ds0b"
  assumes sec: "sec \<le> prf1 + prf2 + ds' + ds + disjointnessT + 
   8 * sqrt( 4 * (1+real (qG+2*qH+qD+1))
                    * real (qG+2*qH+qD+1) * correctness params keygen enc dec msg_space)
   + 2 * correctness params keygen enc dec msg_space"
  shows "sec \<le> prf1 + prf2 + ds0'a+ds0'b + ds0a+ds0b +
   8 * sqrt( 4 * (q+qD+2)
                    * (q+qD+1) * correctness params0 keygen0 enc0 dec0 msg_space0)
   + 2 * correctness params0 keygen0 enc0 dec0 msg_space0"

  using assms unfolding q_def of_nat_mult of_nat_add of_nat_1 of_nat_numeral
  by (smt Rings.mult_sign_intros(1) correctness_punc disjointnessT0 enc0_injective mult_left_mono qD_geq_1 qG_geq_1 qH_geq_1 real_of_nat_ge_one_iff real_sqrt_le_mono)

end
