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
  \<comment> \<open>TODO: it might make proofs easier to add p as parameter.\<close>
  "daemon_step c c' p \<equiv> \<not> c\<cdot>terminated \<and> (
    if (\<exists> p . \<not> (c\<cdot>visited) p) \<or> (\<exists> p q . (c\<cdot>S) p q \<noteq> (c\<cdot>R) q p)
    then c' = c<
      visited := (\<lambda> q . (c\<cdot>visited) q \<or> p = q),
      S := (c\<cdot>S)(p := (c\<cdot>s) p),
      R := (c\<cdot>R)(p := (c\<cdot>r) p)>
    else c' = c<terminated := True> )"

definition step where
  "step c c' \<equiv> \<exists> p . receive_step c c' p \<or> daemon_step c c' p"

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
  have "inv1 c'" if "daemon_step c c' p" and "inv1 c" for p
    using that unfolding daemon_step_def inv1_def 
    by (auto split:if_splits)
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
    by (auto; smt (verit, best) trans_le_add1)
  moreover 
  have "inv2_a c'" if "daemon_step c c' p " and "inv2_a c" for p
  proof -
    have "(c'\<cdot>S) = (c\<cdot>S)(p := (c\<cdot>s) p) \<or> (c'\<cdot>S) = (c\<cdot>S)"
      using \<open>daemon_step c c' p\<close> unfolding daemon_step_def by (auto split: if_splits)
    hence "(c'\<cdot>S) = (c\<cdot>S)(p := (c\<cdot>s) p) \<or> (c'\<cdot>S) = (c\<cdot>S)" by blast
    moreover have "c'\<cdot>s = c\<cdot>s" using \<open>daemon_step c c' p\<close> unfolding daemon_step_def
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
  have "inv2_b c'" if "daemon_step c c' p" and "inv2_b c" for p
  proof -
    have "(c'\<cdot>R) = (c\<cdot>R)(p := (c\<cdot>r) p) \<or> (c'\<cdot>R) = (c\<cdot>R)"
      using \<open>daemon_step c c' p\<close> unfolding daemon_step_def by (auto split: if_splits)
    hence "(c'\<cdot>R) = (c\<cdot>R)(p := (c\<cdot>r) p) \<or> (c'\<cdot>R) = (c\<cdot>R)" by blast
    moreover have "c'\<cdot>r = c\<cdot>r" using \<open>daemon_step c c' p\<close> unfolding daemon_step_def
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
    by (auto; smt (verit, best) trans_le_add1)
  moreover 
  have "inv3 c'" if "daemon_step c c' p" and "inv3 c" for p
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
  define stale where "stale c Q \<equiv> \<exists> p \<in> Q . \<exists> q . (c\<cdot>R) p q \<noteq> (c\<cdot>r) p q \<or> (c\<cdot>S) p q \<noteq> (c\<cdot>s) p q" for c Q
  have "inv4 c'" if "receive_step c c' p " for p
  proof -
    { fix Q
      assume "consistent c' Q" and "stale c' Q"
      have "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c'\<cdot>r) p q > (c'\<cdot>R) p q"
      proof -
        have "consistent c Q" using \<open>consistent c' Q\<close> and \<open>receive_step c c' p\<close>
          unfolding consistent_def receive_step_def by auto
        { assume "stale c Q"
            \<comment> \<open>If Q is stale in @{term c}, then already in @{term c} there is a process that 
has received a message from outside Q that the daemon has not seen. This remains true.}\<close> 
          hence "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c\<cdot>r) p q > (c\<cdot>R) p q" using \<open>inv4 c\<close> \<open>consistent c Q\<close> inv4_def stale_def by auto
          hence ?thesis using \<open>receive_step c c' p\<close> unfolding receive_step_def
            using \<open>inv2_b c\<close> inv2_b_def less_Suc_eq_le by fastforce }
        moreover
        { assume "\<not> (stale c Q)"
            \<comment> \<open>If Q is not stale in @{term c}, then no process in Q can receive a message from another process in Q (because all counts match).
So, because we assume that the count of at least one process in Q changes, it must be by receiving a message from outside Q.}\<close>
          obtain q where "p \<in> Q" and "(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q"
            using \<open>stale c' Q\<close> and \<open>receive_step c c' p\<close> and \<open>\<not> (stale c Q)\<close> 
            unfolding receive_step_def stale_def pending_def 
            apply auto
             apply (smt (verit, best) n_not_Suc_n)+
            done
          moreover
          have "q \<notin> Q"
          proof -
            have "\<forall> p \<in> Q . \<forall> q \<in> Q . (c\<cdot>r) p q = (c'\<cdot>r) p q"
            proof -
              from \<open>\<not> (stale c Q)\<close> have "\<forall> p \<in> Q . \<forall> q \<in> Q . (c\<cdot>s) p q = (c\<cdot>r) q p"
                using \<open>consistent c Q\<close> consistent_def stale_def by force
              thus ?thesis
                using \<open>receive_step c c' p\<close> pending_def unfolding receive_step_def by auto
            qed
            thus ?thesis
              using \<open>(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q\<close>  \<open>p \<in> Q\<close> by auto
          qed
          moreover
          have "(c'\<cdot>r) p q > (c\<cdot>r) p q" using  \<open>(c'\<cdot>r) p q \<noteq> (c\<cdot>r) p q\<close> and \<open>receive_step c c' p\<close>
            unfolding receive_step_def by (auto split:if_splits)
          moreover
          have "(c'\<cdot>R) p q = (c\<cdot>r) p q" using \<open>receive_step c c' p\<close> and \<open>\<not> (stale c Q)\<close> and \<open>p \<in> Q\<close>
            unfolding receive_step_def stale_def by auto
          ultimately
          have ?thesis by force }
        ultimately show ?thesis by auto
      qed }
    thus ?thesis unfolding inv4_def stale_def by blast
  qed
  moreover
  have "inv4 c'" if "daemon_step c c' p" for p
  proof -
    { fix Q
      assume "consistent c' Q" and "stale c' Q"
      have "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c'\<cdot>r) p q > (c'\<cdot>R) p q"
      proof (cases "(\<exists> p . \<not> (c\<cdot>visited) p) \<or> (\<exists> p q . (c\<cdot>S) p q \<noteq> (c\<cdot>R) q p)")
        case True
        then show ?thesis
        proof -
          { assume "p \<notin> Q"
            have "\<exists> p \<in> Q . \<exists> q \<in> -Q . (c\<cdot>r) p q > (c\<cdot>R) p q"
            proof -
              from \<open>p\<notin>Q\<close> have "consistent c Q" and "\<exists> p \<in> Q . \<exists> q . (c\<cdot>R) p q \<noteq> (c\<cdot>r) p q \<or> (c\<cdot>S) p q \<noteq> (c\<cdot>s) p q"
                using \<open>daemon_step c c' p\<close> and \<open>consistent c' Q\<close>
                  and \<open>\<exists> p \<in> Q . \<exists> q . (c'\<cdot>R) p q \<noteq> (c'\<cdot>r) p q \<or> (c'\<cdot>S) p q \<noteq> (c'\<cdot>s) p q\<close>
                unfolding daemon_step_def consistent_def
                by (force split:if_splits)+
              thus ?thesis using \<open>inv4 c\<close> unfolding inv4_def by auto 
            qed
            hence ?thesis using \<open>daemon_step c c' p\<close> and \<open>p \<notin> Q\<close>
              unfolding daemon_step_def by (auto split:if_splits) }
          moreover
          { assume "p \<in> Q"
            have "(c'\<cdot>r) p = (c'\<cdot>R) p" and "(c'\<cdot>s) p = (c'\<cdot>S) p"
              using \<open>daemon_step c c' p\<close> True unfolding daemon_step_def
              by auto
            define Q' where "Q' \<equiv> Q - {p}"
            have "consistent c Q'"
              using \<open>daemon_step c c' p\<close> True \<open>consistent c' Q\<close>
              unfolding daemon_step_def consistent_def Q'_def
              by (auto; (smt (verit)))
            have "stale c Q'"
              using \<open>daemon_step c c' p\<close> True \<open>stale c' Q\<close>
              unfolding daemon_step_def Q'_def stale_def
              by (auto split:if_splits)
            have ?thesis sorry }
          ultimately show ?thesis by blast
        qed
      next
        case False
        then show ?thesis 
          using \<open>daemon_step c c' p\<close> and \<open>consistent c' Q\<close>
            and \<open>stale c' Q\<close>
            and \<open>inv4 c\<close>
          unfolding daemon_step_def consistent_def inv4_def stale_def
          by auto
      qed }
    thus ?thesis
      using inv4_def stale_def by blast 
  qed
  ultimately show ?thesis 
    using assms(1) unfolding step_def by blast
qed

end

end