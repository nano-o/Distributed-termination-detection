theory Termination
  imports Main "HOL-Statespace.StateSpaceSyntax"
begin

statespace 'p vars = 
  s :: "'p \<Rightarrow> 'p \<Rightarrow> nat"
  S :: "'p \<Rightarrow> 'p \<Rightarrow> nat"
  r :: "'p \<Rightarrow> 'p \<Rightarrow> nat"
  R :: "'p \<Rightarrow> 'p \<Rightarrow> nat"
  visited :: "'p \<Rightarrow> bool"
  terminated :: bool

context vars
begin

definition pending where
  \<comment> \<open>Number of messages in flight from p to q\<close>
  "pending c p q \<equiv> ((c\<cdot>s) p q) - ((c\<cdot>r) q p)"

definition receive_step where
  \<comment> \<open>Process p receives a message from q and sends a few more messages in response.\<close>
  "receive_step c c' p \<equiv> \<exists> q .
    p \<noteq> q 
    \<and> pending c q p > 0
    \<and> (\<exists> P . \<comment> \<open>We pick a set P of processes to send messages to.\<close>
        \<exists> s_p' . s_p' = (\<lambda> q .
            let s_p_q = ((c\<cdot>s) p q)
            in if q \<in> P - {p} then s_p_q + 1 else s_p_q)
    \<comment> \<open>Note, above, that a process doesn't send a message to itself.\<close>
    \<comment> \<open>Now we describe the new state:\<close>
        \<and> c' = c<s := (c\<cdot>s)(p:=s_p'), r := (c\<cdot>r)(p:=((c\<cdot>r) p)(q := (c\<cdot>r) p q + 1))>)"

definition daemon_step where
  "daemon_step c c' \<equiv> \<not> c\<cdot>terminated \<and> (
    if (\<exists> p . \<not> (c\<cdot>visited) p) \<or> (\<exists> p q . (c\<cdot>S) p q \<noteq> (c\<cdot>R) q p)
    then \<exists> p . c' = c<
      visited := (\<lambda> q . (c\<cdot>visited) q \<or> p = q),
      S := (c\<cdot>S)(p := (c\<cdot>s) p),
      R := (c\<cdot>R)(p := (c\<cdot>r) p)>
    else c' = c<terminated := True> )"

definition step where
  "step c c' \<equiv> (\<exists> p . receive_step c c' p) \<or> daemon_step c c'"

definition inv1 where
  "inv1 c \<equiv> \<forall> p . (c\<cdot>visited) p \<or> (\<forall> q . (c\<cdot>S) p q = 0 \<and> (c\<cdot>R) p q = 0)"

lemma inv1_step:
  assumes "step c c'" and "inv1 c"
  shows "inv1 c'"
proof -
  have "inv1 c'" if "receive_step c c' p " and "inv1 c" for p
    using that unfolding receive_step_def inv1_def 
    by force
  moreover
  have "inv1 c'" if "daemon_step c c'" and "inv1 c"
    using that unfolding daemon_step_def inv1_def 
    apply auto
    apply (smt (z3) HOL_bool_'p_fun.project_inject_axioms K_statefun_apply Nat_nat_'p_fun_'p_fun.project_inject_axioms all_distinct_right distinct_left_right distinct_names distinct_right fun_upd_other in_set_right in_set_root lookup_update_other lookup_update_same project_inject_def)
    apply (smt (z3) HOL_bool_'p_fun.project_inject_axioms K_statefun_def Nat_nat_'p_fun_'p_fun.project_inject_axioms all_distinct_right distinct_left_right distinct_names distinct_right fun_upd_other in_set_right in_set_root lookup_update_other lookup_update_same project_inject_def)
    done
  ultimately show ?thesis
    using assms step_def by blast
qed

definition inv2_a where
  "inv2_a c \<equiv> \<forall> p q . (c\<cdot>S) p q \<le> (c\<cdot>s) p q"

lemma inv2_a_step:
  assumes "step c c'" and "inv2_a c"
  shows "inv2_a c'"
proof -
  have "inv2_a c'" if "receive_step c c' p " and "inv2_a c" for p
    using that unfolding receive_step_def inv2_a_def
    by (smt (verit, del_insts) K_statefun_def Nat_nat_'p_fun_'p_fun.project_inject_cancel add_increasing2 distinct_left distinct_names fun_upd_apply in_set_right in_set_root leI less_one lookup_update_other lookup_update_same nless_le)
  moreover 
  have "inv2_a c'" if "daemon_step c c'" and "inv2_a c"
  proof -
    have "\<exists> p . (c'\<cdot>S) = (c\<cdot>S)(p := (c\<cdot>s) p) \<or> (c'\<cdot>S) = (c\<cdot>S)"
      using \<open>daemon_step c c'\<close> unfolding daemon_step_def by (auto split: if_splits)
    with this obtain p where "(c'\<cdot>S) = (c\<cdot>S)(p := (c\<cdot>s) p) \<or> (c'\<cdot>S) = (c\<cdot>S)" by blast
    moreover have "c'\<cdot>s = c\<cdot>s" using \<open>daemon_step c c'\<close> unfolding daemon_step_def
      by (auto split:if_splits)
    ultimately show ?thesis using \<open>inv2_a c\<close> unfolding inv2_a_def by auto
  qed
  ultimately show ?thesis
    using assms step_def by blast
qed

definition inv2_b where
  "inv2_b c \<equiv> \<forall> p q . (c\<cdot>R) p q \<le> (c\<cdot>r) p q"

lemma inv2_b_step:
  assumes "step c c'" and "inv2_b c"
  shows "inv2_b c'"
proof -
  have "inv2_b c'" if "receive_step c c' p " and "inv2_b c" for p
    using that unfolding receive_step_def inv2_b_def
    using nat_le_linear not_less_eq_eq by fastforce
  moreover 
  have "inv2_b c'" if "daemon_step c c'" and "inv2_b c"
  proof -
    have "\<exists> p . (c'\<cdot>R) = (c\<cdot>R)(p := (c\<cdot>r) p) \<or> (c'\<cdot>R) = (c\<cdot>R)"
      using \<open>daemon_step c c'\<close> unfolding daemon_step_def by (auto split: if_splits)
    with this obtain p where "(c'\<cdot>R) = (c\<cdot>R)(p := (c\<cdot>r) p) \<or> (c'\<cdot>R) = (c\<cdot>R)" by blast
    moreover have "c'\<cdot>r = c\<cdot>r" using \<open>daemon_step c c'\<close> unfolding daemon_step_def
      by (auto split:if_splits)
    ultimately show ?thesis using \<open>inv2_b c\<close> unfolding inv2_b_def by auto
  qed
  ultimately show ?thesis
    using assms step_def by blast
qed

definition inv3 where
  "inv3 c \<equiv> \<forall> p q . (c\<cdot>r) p q \<le> (c\<cdot>s) q p"

lemma inv3_step:
  assumes "step c c'" and "inv3 c"
  shows "inv3 c'"
proof -
  have "inv3 c'" if "receive_step c c' p " and "inv3 c" for p
    using that unfolding receive_step_def pending_def inv3_def
    by (smt (verit) K_statefun_def Nat_nat_'p_fun_'p_fun.project_inject_cancel Suc_eq_plus1 Suc_leI fun_upd_apply lookup_update_other lookup_update_same trans_le_add1 zero_less_diff)
  moreover 
  have "inv3 c'" if "daemon_step c c'" and "inv3 c"
    using that unfolding daemon_step_def inv3_def
    by (auto split:if_splits)
  ultimately show ?thesis
    using assms step_def by blast
qed

definition consistent where
  "consistent c Q \<equiv> \<forall> p \<in> Q . (c\<cdot>visited) p \<and> (\<forall> q \<in> Q . (c\<cdot>S) p q = (c\<cdot>R) q p)"

definition inv4 where
  "inv4 c \<equiv> \<forall> Q . consistent c Q \<and> (\<exists> p \<in> Q . \<exists> q . (c\<cdot>R) p q \<noteq> (c\<cdot>r) p q \<or> (c\<cdot>S) p q \<noteq> (c\<cdot>s) p q)
    \<longrightarrow> (\<exists> p \<in> Q . \<exists> q \<in> -Q . (c\<cdot>r) p q > (c\<cdot>R) p q)"

lemma inv4_step:
  assumes "step c c'" and "inv1 c" and "inv2_a c" and "inv2_b c" and "inv3 c" "inv4 c"
  shows "inv4 c'"
proof -
  have "inv4 c'" if "receive_step c c' p " for p
  proof -
    { fix Q
      assume "consistent c' Q" and "\<exists> p \<in> Q . \<exists> q . (c'\<cdot>R) p q \<noteq> (c'\<cdot>r) p q \<or> (c'\<cdot>S) p q \<noteq> (c'\<cdot>s) p q"
      have "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c'\<cdot>r) p q > (c'\<cdot>R) p q"
      proof -
        have "consistent c Q" using \<open>consistent c' Q\<close> and \<open>receive_step c c' p\<close>
          unfolding consistent_def receive_step_def by auto
        define stale where "stale \<equiv> \<exists> p \<in> Q . \<exists> q . (c\<cdot>R) p q \<noteq> (c\<cdot>r) p q \<or> (c\<cdot>S) p q \<noteq> (c\<cdot>s) p q"
        { assume stale
            \<comment> \<open>If Q is stale in @{term c}, then already in @{term c} there is a process that 
has received a message from outside Q that the daemon has not seen. This remains true.}\<close> 
          hence "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c\<cdot>r) p q > (c\<cdot>R) p q" using \<open>inv4 c\<close> \<open>consistent c Q\<close> inv4_def stale_def by blast
          hence ?thesis using \<open>receive_step c c' p\<close> unfolding receive_step_def
            using \<open>inv2_b c\<close> inv2_b_def less_Suc_eq_le by fastforce }
        moreover
        { assume "\<not>stale"
            \<comment> \<open>If Q is not stale in @{term c}, then no process in Q can receive a message from another process in Q (because all counts match).
So, because we assume that the count of at least one process in Q changes, it must be by receiving a message from outside Q.}\<close>
          hence "\<forall> p \<in> Q . \<forall> q \<in> Q . (c\<cdot>s) p q = (c\<cdot>r) q p"
            using \<open>consistent c Q\<close> consistent_def stale_def by force
          hence "\<forall> p \<in> Q . \<forall> q \<in> Q . (c\<cdot>r) p q = (c'\<cdot>r) p q"
            using \<open>receive_step c c' p\<close> pending_def unfolding receive_step_def by auto
          obtain q where "p \<in> Q" and "(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q"
            using \<open>\<exists> p \<in> Q . \<exists> q . (c'\<cdot>R) p q \<noteq> (c'\<cdot>r) p q \<or> (c'\<cdot>S) p q \<noteq> (c'\<cdot>s) p q\<close>
              and \<open>receive_step c c' p\<close> and \<open>\<not>stale\<close>
            unfolding receive_step_def stale_def pending_def 
            apply auto
             apply (smt (verit, best) n_not_Suc_n)+
            done
          have "q \<notin> Q" using \<open>\<forall> p \<in> Q . \<forall> q \<in> Q . (c\<cdot>r) p q = (c'\<cdot>r) p q\<close> \<open>(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q\<close>  \<open>p \<in> Q\<close> by auto
          have "(c'\<cdot>r) p q > (c\<cdot>r) p q" using  \<open>(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q\<close> and \<open>receive_step c c' p\<close>
            unfolding receive_step_def by (auto split:if_splits)
          have "(c'\<cdot>R) p q = (c\<cdot>r) p q" using \<open>receive_step c c' p\<close> and \<open>\<not>stale\<close> and \<open>p \<in> Q\<close>
            unfolding receive_step_def stale_def by auto
          have ?thesis using \<open>(c'\<cdot>R) p q = (c\<cdot>r) p q\<close> and \<open>(c'\<cdot>r) p q > (c\<cdot>r) p q\<close> and \<open>p \<in> Q\<close> and \<open>q \<notin> Q\<close>
            by force }
        ultimately show ?thesis by auto
      qed  }
    thus ?thesis unfolding inv4_def by blast
  qed
  moreover
  have "inv4 c'" if "daemon_step c c'"  sorry
  ultimately show ?thesis 
    using assms(1) unfolding step_def by blast
qed

end

end