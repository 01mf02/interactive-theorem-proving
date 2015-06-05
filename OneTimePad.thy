theory OneTimePad imports
  "HOL/Probability"
  "HOL/Groups_Big"
begin

type_synonym key     = "int list"
type_synonym message = "int list"
type_synonym crypted = "int list"

definition zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"

(*primrec zipWith where
  "zipWith f [] ys = (case ys of [] \<Rightarrow> [])"
| "zipWith f (x # xs) zs = (case zs of y # ys \<Rightarrow> f x y # zipWith f xs ys)"

lemma "length xs = length ys \<Longrightarrow> zipWith f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"
by (induct xs ys rule: list_induct2, auto)*)

definition encrypt :: "message \<Rightarrow> key \<Rightarrow> crypted" where
  "encrypt = zipWith plus"

definition decrypt :: "crypted \<Rightarrow> key \<Rightarrow> message" where
  "decrypt = zipWith minus"
  
definition reconstruct_key :: "crypted \<Rightarrow> message \<Rightarrow> key" where
  "reconstruct_key = zipWith minus"
  

lemma "length m = length k \<Longrightarrow> decrypt (encrypt m k) k = m"
unfolding encrypt_def decrypt_def zipWith_def
by (induct m k rule: list_induct2, auto)

lemma "length m = length k \<Longrightarrow> length (encrypt m k) = length m"
unfolding encrypt_def zipWith_def
by (induct m k rule: list_induct2, auto)

lemma reconstruct:
  assumes "length m = length c"
    shows "length (reconstruct_key c m) = length m"
      and "encrypt m (reconstruct_key c m) = c"
unfolding encrypt_def reconstruct_key_def zipWith_def
using assms by (induct m c rule: list_induct2, auto)

lemma test:
  assumes "length m = length c"
    shows "\<exists>!k. length m = length k \<and> encrypt m k = c"
proof (intro ex1I)
  show "length m = length (reconstruct_key c m) \<and>
        encrypt m (reconstruct_key c m) = c"
        using reconstruct[OF assms] by auto
next
  show "\<And>k. length m = length k \<and> encrypt m k = c \<Longrightarrow> k = reconstruct_key c m"
  (*unfolding encrypt_def reconstruct_key_def zipWith_def
  apply (induct m k rule: list_induct2)*)
  sorry
qed



axiomatization
      \<K> :: "key set"
  and \<M> :: "message set"
  and P\<^sub>\<K> :: "key pmf"
  and P\<^sub>\<M> :: "message pmf"
  and len :: nat
where k_finite: "finite \<K>"
  and m_finite: "finite \<M>"
  and k_nonemp: "\<K> \<noteq> {}"
  and m_nonemp: "\<M> \<noteq> {}"
  and k_length: "\<forall>k\<in>\<K>. length k = len"
  and m_length: "\<forall>m\<in>\<M>. length m = len"
  and k_unipmf: "P\<^sub>\<K> = pmf_of_set \<K>"  (* uniform distribution *)

definition \<P>\<^sub>\<K> :: "key \<Rightarrow> real" where "\<P>\<^sub>\<K> = pmf P\<^sub>\<K>"
definition \<P>\<^sub>\<M> :: "message \<Rightarrow> real" where "\<P>\<^sub>\<M> = pmf P\<^sub>\<M>"

lemma "k \<in> \<K> \<Longrightarrow> \<P>\<^sub>\<K> k = 1 / card \<K>"
unfolding \<P>\<^sub>\<K>_def k_unipmf pmf_of_set[OF k_nonemp k_finite] by auto


(* probability of cryptogram c if message m is chosen *)
definition \<P>\<^sub>\<M>\<^sub>\<C> :: "message \<Rightarrow> crypted \<Rightarrow> real" where
  "\<P>\<^sub>\<M>\<^sub>\<C> m c = (\<Sum>k | k\<in>\<K> \<and> length k = length m \<and> encrypt m k = c. \<P>\<^sub>\<K> k)"

lemma "\<P>\<^sub>\<M>\<^sub>\<C> m c = 1 / card \<K>"
sorry

(* probability of obtaining cryptogram c from any cause *)
definition \<P>\<^sub>\<C> :: "crypted \<Rightarrow> real" where
  "\<P>\<^sub>\<C> c = (\<Sum>m\<in>\<M>. \<P>\<^sub>\<M> m * \<P>\<^sub>\<M>\<^sub>\<C> m c)"

theorem "\<P>\<^sub>\<M>\<^sub>\<C> m c = \<P>\<^sub>\<C> c"
sorry


(*theorem "\<lbrakk> length m = length k; length m = length k'; m \<noteq> []; c = encrypt m k; k \<noteq> k' \<rbrakk>
  \<Longrightarrow> decrypt c k' \<noteq> m"*)


end
