theory BTree_Index
imports Main
begin

datatype 'a btree = Leaf | Node "'a list" "'a btree list"

fun split_linear_help where
"split_linear_help a [] n = n" |
"split_linear_help a (x#xs) n = (if a \<le> x then n else (split_linear_help a xs (Suc n)))"

fun split_linear where
"split_linear a l = split_linear_help a l 0"

value "split_linear (1::nat) [1,1,2]"

lemma "sorted l \<Longrightarrow> \<forall>x \<in> set (take ((split_linear_help a l k)-k) l). x < a"
  apply(induction a l k rule: split_linear_help.induct)
   apply(auto)
  by (metis Suc_diff_Suc diff_is_0_eq' empty_iff le_less_linear list.set(1) set_ConsD take_Cons' take_Suc_Cons)

lemma "strict_sorted l \<Longrightarrow> \<forall>x \<in> set (drop ((split_linear_help a l k)+k+1) l). x > a"
  apply(induction a l k rule: split_linear_help.induct)
   apply(auto)
  using in_set_dropD apply fastforce
  oops


end