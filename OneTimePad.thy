theory OneTimePad imports
  "HOL/Probability"
  "HOL/Groups_Big"
begin

type_synonym key     = "bool list"
type_synonym message = "bool list"
type_synonym crypted = "bool list"

definition zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"

(*primrec zipWith where
  "zipWith f [] ys = (case ys of [] \<Rightarrow> [])"
| "zipWith f (x # xs) zs = (case zs of y # ys \<Rightarrow> f x y # zipWith f xs ys)"

lemma "length xs = length ys \<Longrightarrow> zipWith f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"
by (induct xs ys rule: list_induct2, auto)*)

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor = not_equal"

definition encrypt :: "message \<Rightarrow> key \<Rightarrow> crypted" where
  "encrypt = zipWith xor"

definition decrypt :: "crypted \<Rightarrow> key \<Rightarrow> message" where
  "decrypt = zipWith xor"
  
definition reconstruct_key :: "crypted \<Rightarrow> message \<Rightarrow> key" where
  "reconstruct_key = zipWith xor"
  

lemma enc:
  assumes "length m = length k"
    shows "length (encrypt m k) = length m"
      and "decrypt (encrypt m k) k = m"
unfolding encrypt_def decrypt_def zipWith_def xor_def
using assms by (induct m k rule: list_induct2, auto)


lemma reconstruct:
  assumes "length m = length c"
    shows "length (reconstruct_key c m) = length m"
      and "encrypt m (reconstruct_key c m) = c"
unfolding encrypt_def reconstruct_key_def zipWith_def xor_def
using assms by (induct m c rule: list_induct2, auto)

lemma rec_uniq:
  assumes "length m = length k"
      and "encrypt m k = c"
    shows "k = reconstruct_key c m"
proof -
  have L: "length k = length c" using enc(1) assms(1) assms(2) by auto
  show ?thesis using assms(1) L assms(2) unfolding encrypt_def reconstruct_key_def zipWith_def xor_def
    by (induct m k c rule: list_induct3, auto)
qed

lemma uniq_key:
  assumes "length m = length c"
    shows "\<exists>!k. length m = length k \<and> encrypt m k = c"
using reconstruct[OF assms] rec_uniq by (intro ex1I[of _ "reconstruct_key c m"], auto)

axiomatization
      \<K> :: "key set"
  and \<M> :: "message set"
  and P\<^sub>\<K> :: "key pmf"
  and P\<^sub>\<M> :: "message pmf"
  and len :: nat
where k_unipmf: "P\<^sub>\<K> = pmf_of_set \<K>"  (* uniform distribution *)
  and m_pmf: "set_pmf P\<^sub>\<M> \<subseteq> \<M>"
  and k_set: "\<K> = set (List.n_lists len [True, False])"
  and m_set: "\<M> = \<K>"

definition \<P>\<^sub>\<K> :: "key \<Rightarrow> real" where "\<P>\<^sub>\<K> = pmf P\<^sub>\<K>"
definition \<P>\<^sub>\<M> :: "message \<Rightarrow> real" where "\<P>\<^sub>\<M> = pmf P\<^sub>\<M>"

lemma k_finite: "finite \<K>"
by (metis List.finite_set k_set)

lemma k_nonemp: "\<K> \<noteq> {}"
unfolding k_set set_n_lists by (simp add: Ex_list_of_length subsetI)

lemma k_length: "\<forall>k\<in>\<K>. length k = len"
unfolding k_set using length_n_lists_elem by auto

lemma k_in_k: "k \<in> \<K> \<longleftrightarrow> (length k = len)"
proof (rule iffI)
  assume "k \<in> \<K>"
  then show "length k = len" unfolding k_set using length_n_lists_elem by auto
next
  assume "length k = len"
  then show "k \<in> \<K>" unfolding k_set set_n_lists by auto
qed

lemma pmf_sum_one:
  assumes "finite M"
      and "set_pmf P \<subseteq> M"
    shows "(\<Sum>m\<in>M. pmf P m) = 1"
proof -
  have "(\<Sum>m\<in>M. pmf P m) = measure (measure_pmf P) M"
    using assms(1) by (simp add: measure_measure_pmf_finite)
  show ?thesis sorry
qed

lemma m_sum_one: "(\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m) = 1"
using pmf_sum_one[of \<M> P\<^sub>\<M>] k_finite m_pmf unfolding \<P>\<^sub>\<M>_def m_set by auto


lemma k_prob: "k \<in> \<K> \<Longrightarrow> \<P>\<^sub>\<K> k = 1 / card \<K>"
unfolding \<P>\<^sub>\<K>_def k_unipmf pmf_of_set[OF k_nonemp k_finite] by auto


(* probability of cryptogram c if message m is chosen *)
definition \<P>\<^sub>\<M>\<^sub>\<C> :: "message \<Rightarrow> crypted \<Rightarrow> real" where
  "\<P>\<^sub>\<M>\<^sub>\<C> m c = (\<Sum>k | k \<in> \<K> \<and> encrypt m k = c. \<P>\<^sub>\<K> k)"

lemma set_singleton:
  assumes "\<forall>x \<in> S. (P x \<longrightarrow> x = y)"
      and "\<exists>x \<in> S.  P x"
    shows "{x \<in> S. P x} = {y}"
by (smt Collect_cong Set.ball_empty assms insert_compr)

lemma rec_in_k:
  assumes "m \<in> \<M>"
      and "length m = length c"
    shows "reconstruct_key c m \<in> \<K>"
proof -
  have "length m = len" using assms(1) k_length m_set by auto
  then have "length (reconstruct_key c m) = len" using reconstruct(1)[OF assms(2)] by auto
  then show ?thesis using k_in_k by auto
qed

lemma uniq_k:
  assumes "m \<in> \<M>"
      and "length m = length c"
    shows "{k \<in> \<K>. encrypt m k = c} = {reconstruct_key c m}"
proof (rule set_singleton)
  show "\<exists>k\<in>\<K>. encrypt m k = c"
  proof (rule bexI[of _ "reconstruct_key c m"])
    show "encrypt m (reconstruct_key c m) = c" using reconstruct(2)[OF assms(2)] .
    show "reconstruct_key c m \<in> \<K>" using rec_in_k[OF assms] by auto
  qed
  show "\<forall>k\<in>\<K>. encrypt m k = c \<longrightarrow> k = reconstruct_key c m"
  proof (rule ballI)
    fix k
    assume K: "k \<in> \<K>"
    then have "length k = len" using k_in_k by auto
    also have "length m = len" using assms(1) k_in_k unfolding m_set by auto
    finally have "length m = length k" .
    then show "encrypt m k = c \<longrightarrow> k = reconstruct_key c m" using rec_uniq by auto
  qed
qed

lemma pmc_card_k:
  assumes "m \<in> \<M>"
      and "length c = len"
    shows "\<P>\<^sub>\<M>\<^sub>\<C> m c = 1 / card \<K>"
proof -
  have L: "length m = length c" using k_in_k m_set assms by auto
  have K: "(reconstruct_key c m) \<in> \<K>" using rec_in_k[OF assms(1) L] .
  have "\<P>\<^sub>\<K> (reconstruct_key c m) = 1 / real (card \<K>)" using k_prob[OF K] .
  then show ?thesis unfolding \<P>\<^sub>\<M>\<^sub>\<C>_def unfolding uniq_k[OF assms(1) L] by simp
qed

(* probability of obtaining cryptogram c from any cause *)
definition \<P>\<^sub>\<C> :: "crypted \<Rightarrow> real" where
  "\<P>\<^sub>\<C> c = (\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m * \<P>\<^sub>\<M>\<^sub>\<C> m c)"

theorem
  assumes "m \<in> \<M>"
      and "length c = len"
    shows "\<P>\<^sub>\<M>\<^sub>\<C> m c = \<P>\<^sub>\<C> c"
proof -
  have "\<P>\<^sub>\<C> c = (\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m * \<P>\<^sub>\<M>\<^sub>\<C> m c)" unfolding \<P>\<^sub>\<C>_def by auto
  also have "... = (\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m * 1 / card \<K>)" using pmc_card_k[OF _ assms(2)] by auto
  also have "... = (\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m) / card \<K>" by (smt setsum.cong setsum_divide_distrib)
  also have "... = 1 / card \<K>" using m_sum_one by simp
  finally have "\<P>\<^sub>\<C> c = 1 / real (card \<K>)" by auto
  then show ?thesis using pmc_card_k[OF assms] by simp
qed

end
