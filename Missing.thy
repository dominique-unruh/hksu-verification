theory Missing
  imports QRHL.QRHL
begin

(* lemma MAXIMUM_mono:
  assumes finite: "finite B"
  assumes nonempty: "A \<noteq> {}"
  assumes subset: "A \<subseteq> B"
  assumes leq: \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x\<close>
  shows "(MAX x\<in>A. f x) \<le> (MAX x\<in>B. g x)"
proof -
  from finite subset have \<open>finite A\<close>
    using finite_subset by blast
  then have \<open>Max (f ` A) \<le> Max (g ` A)\<close>
  proof (insert leq, induction)
    case empty
    show ?case by simp
  next
    case (insert x F)
    show ?case
    proof (cases "F={}")
      case True
      with insert show ?thesis by simp
    next
      case False
      have "Max (f ` insert x F) = max (f x) (Max (f ` F))"
        apply simp apply (subst Max_insert) using insert False by auto 
      also have "\<dots> \<le> max (g x) (Max (g ` F))"
        using insert by (meson insert_iff max.mono) 
      also have "\<dots> = Max (g ` (insert x F))"
        apply simp apply (subst Max_insert) using insert False by auto 
      finally show ?thesis .
    qed
  qed
  moreover have \<open>Max (g ` A) \<le> Max (g ` B)\<close>
    apply (rule Max_mono)
    using subset nonempty finite by auto
  finally show ?thesis .
qed *)

lemma TERM: "TERM (x::prop) == Trueprop True"
  unfolding term_def by (rule, auto)

end
