theory General_Definitions
  imports QRHL.QRHL Missing
begin

definition "force_into M x = (if x\<in>M then x else SOME m. m\<in>M)"

definition correctness_pkskm where    
  "correctness_pkskm enc dec p pk sk m = Prob (enc p pk m) {c. dec p sk c \<noteq> Some m}"

(* In the paper, this is a maximum. We use supremum since, in principle, one could have an infinite message space. *)
definition correctness_pksk where
  "correctness_pksk enc dec msg_space p pk sk = 
    (SUP m\<in>msg_space p. correctness_pkskm enc dec p pk sk m)"


\<comment> \<open>P = distribution of public parameters / oracles, enc = probabilistic encryption algorithm 
    / dec = deterministic decryption algorithm / msg_space = message space\<close>
definition correctness where
  "correctness P keygen enc dec msg_space = 
      expectation' P (\<lambda>p. 
      expectation' (keygen p) (\<lambda>(pk,sk). correctness_pksk enc dec msg_space p pk sk))"

\<comment> \<open>P = distribution of public parameters / oracles, encaps = probabilistic encapsulation algorithm 
    / decaps = deterministic decapsulation algorithm\<close>
definition KEMcorrectness where
  "KEMcorrectness P keyspace keygen encaps decaps =
  prob
  (bind_distr P (\<lambda>p. bind_distr (keygen p) (\<lambda>(pk,sk). (map_distr (\<lambda>(K,c). decaps p sk c \<noteq> Some K \<or> K \<notin> keyspace p) (encaps p pk)))))
  True"

definition "disjointness P keygen enc fakeenc msg_space = (\<Squnion>p\<in>supp P. \<Squnion>(pk,sk)\<in>supp (keygen p). 
  Prob (fakeenc p pk) (\<Union>m\<in>msg_space p. supp (enc p pk m)))"


(* Deviating from paper: only for pk<-keygen, no recovery of randomness *)
definition "injective_enc_pk p enc msg_space pk \<longleftrightarrow> 
  (\<forall>m1\<in>msg_space p. \<forall>m2\<in>msg_space p. disjnt (supp (enc p pk m1)) (supp (enc p pk m2)))"
definition "injective_enc P keygen enc msg_space \<longleftrightarrow>
  (\<forall>p\<in>supp P. \<forall>(pk,sk)\<in>supp (keygen p). injective_enc_pk p enc msg_space pk)"




axiomatization qD qG qH :: nat
  where qD_geq_1[simp]: "qD \<ge> 1"
    and qG_geq_1[simp]: "qG \<ge> 1"
    and qH_geq_1[simp]: "qH \<ge> 1"

definition "q = qG + 2 * qH"

end
