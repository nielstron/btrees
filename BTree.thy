theory BTree                 
  imports Main "HOL-Data_Structures.Sorted_Less" "HOL-Data_Structures.Cmp"
begin

hide_const (open) Sorted_Less.sorted
abbreviation "sorted_less \<equiv> Sorted_Less.sorted"

subsection "General structure and concepts definition"

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
  (* definition heavily based on Tree234_Set, Pair structure from popl10 (malecha)/mtps08*)


datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

type_synonym 'a btree_list =  "('a btree * 'a) list"
type_synonym 'a btree_pair =  "('a btree * 'a)"

fun inorder :: "'a btree \<Rightarrow> 'a list" where
  "inorder Leaf = []" |
  "inorder (Node ts t) = concat (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) @ inorder t"

abbreviation "inorder_pair  \<equiv> \<lambda>(sub,sep). inorder sub @ [sep]"
abbreviation "inorder_list ts \<equiv> concat (map inorder_pair ts)"


(* this abbreviation makes handling the list much easier *)
thm inorder.simps

abbreviation subtrees where "subtrees xs \<equiv> (map fst xs)"
abbreviation separators where "separators xs \<equiv> (map snd xs)"
abbreviation "set_btree_pair uu \<equiv> (\<Union>(set_btree ` Basic_BNFs.fsts uu) \<union> Basic_BNFs.snds uu)"
abbreviation "set_btree_list ts \<equiv> (\<Union>uu\<in>set ts. set_btree_pair uu)"



class height =
  fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: (type) height
begin

fun height_btree :: "'a btree \<Rightarrow> nat" where
  "height Leaf = 0" |
  "height (Node ts t) = Suc (Max (height ` (set (subtrees ts@[t]))))"

instance ..

end

thm btree.set

fun bal:: "'a btree \<Rightarrow> bool" where
  "bal Leaf = True" |
  "bal (Node ts t) = (
    (\<forall>sub \<in> set (subtrees ts). height t = height sub) \<and>
    (\<forall>sub \<in> set (subtrees ts). bal sub) \<and>
    bal t
  )"


(* alt1: following knuths definition to allow for any natural number as order and resolve ambiguity *)
(* alt2: use range [k,2*k] allowing for valid btrees from k=1 onwards *)
(* TODO allow for length ts \<le> 2*k+1, NOTE: makes proofs uglier *)
fun order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
  "order k Leaf = True" |
  "order k (Node ts t) = (
  (length ts \<ge> k)  \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>sub \<in> set (subtrees ts). order k sub) \<and>
  order k t
)"


(* the invariant for the root of the btree *)
fun root_order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
  "root_order k Leaf = True" |
  "root_order k (Node ts t) = (
  (length ts > 0) \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and>
   order k t
)"




(* auxiliary lemmas when handling sets *)
lemma separators_split:
  "set (separators (l@(a,b)#r)) = set (separators l) \<union> set (separators r) \<union> {b}"
  by simp

lemma subtrees_split:
  "set (subtrees (l@(a,b)#r)) = set (subtrees l) \<union> set (subtrees r) \<union> {a}"
  by simp

(* height and set lemmas *)

lemma height_Leaf: "height t = 0 \<longleftrightarrow> t = Leaf"
  by (induction t) (auto)


lemma height_btree_order:
  "height (Node (ls@[a]) t) = height (Node (a#ls) t)"
  by simp

lemma height_btree_sub: 
  "height (Node ((sub,x)#ls) t) = max (height (Node ls t)) (Suc (height sub))"
  by simp

lemma height_btree_last: 
  "height (Node ((sub,x)#ts) t) = max (height (Node ts sub)) (Suc (height t))"
  by (induction ts) auto


value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"


lemma set_btree_inorder: "set (inorder t) = set_btree t"
  apply(induction t)
   apply(auto)
  done


lemma child_subset: "p \<in> set t \<Longrightarrow> set_btree (fst p) \<subseteq> set_btree (Node t n)"
  apply(induction p arbitrary: t n)
  apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
    and "sep \<in> set (separators t)"
  using assms by force+ 

(* balancedness lemmas *)


lemma bal_all_subtrees_equal: "bal (Node ts t) \<Longrightarrow> (\<forall>s1 \<in> set (subtrees ts). \<forall>s2 \<in> set (subtrees ts). height s1 = height s2)"
  by (metis BTree.bal.simps(2))


lemma fold_max_set: "\<forall>x \<in> set t. x = f \<Longrightarrow> fold max t f = f"
  apply(induction t)
   apply(auto simp add: max_def_raw)
  done

lemma height_bal_tree: "bal (Node ts t) \<Longrightarrow> height (Node ts t) = Suc (height t)"
  by (induction ts) auto
 


lemma bal_split_last: 
  assumes "bal (Node (ls@(sub,sep)#rs) t)"
  shows "bal (Node (ls@rs) t)"
    and "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
proof -
  from assms have
    "bal t"
    "\<forall>sub \<in> set (subtrees (ls@(sub,sep)#rs)). height t = height sub \<and> bal sub"
    using bal.simps(2) by blast+
  moreover have "\<forall>sub \<in> set (subtrees ls) \<union> set (subtrees rs). height t = height sub \<and> bal sub"
    using subtrees_split
    by (simp add: calculation)
  ultimately show
    "bal (Node (ls@rs) t)"
    by auto
  then show "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
    using height_bal_tree assms by metis
qed


lemma bal_split_right: 
  assumes "bal (Node (ls@rs) t)"
  shows "bal (Node rs t)"
    and "height (Node rs t) = height (Node (ls@rs) t)"
proof -
  show "bal (Node rs t)"
    using assms by auto
  then show "height (Node rs t) = height (Node (ls@rs) t)"
    using height_bal_tree assms
    by metis
qed

lemma bal_split_left:
  assumes "bal (Node (ls@(a,b)#rs) t)"
  shows "bal (Node ls a)"
    and "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
proof -
  from assms have "\<forall>x \<in> set (subtrees ls). height x = height t"
    using subtrees_split by force
  then show "bal (Node ls a)"
    using assms by auto
  moreover have "height a = height t"
    using assms by auto
  ultimately show "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
    using assms height_bal_tree
    by metis
qed


lemma bal_substitute: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height t = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  unfolding bal.simps
  by (metis Un_iff singletonD subtrees_split)

lemma bal_substitute_subtree: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height a = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  using bal_substitute
  by (metis bal.simps(2) in_set_conv_decomp some_child_sub(1))

lemma bal_substitute_separator: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal (Node (ls@(a,c)#rs) t)"
  unfolding bal.simps
  by (metis subtrees_split)

(* order lemmas *)

lemma order_impl_root_order: "\<lbrakk>k > 0; order k t\<rbrakk> \<Longrightarrow> root_order k t"
  apply(cases t)
   apply(auto)
  done


value "set (inorder (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf))"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"
  (* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"



(* sorted inorder implies that some sublists are sorted which can be followed directly *)

lemma sorted_inorder_list_separators: "sorted_less (inorder_list ts) \<Longrightarrow> sorted_less (separators ts)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)
  done

corollary sorted_inorder_separators: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (separators ts)"
  using sorted_inorder_list_separators sorted_wrt_append
  by auto


lemma sorted_inorder_list_subtrees:
  "sorted_less (inorder_list ts) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)+
  done

corollary sorted_inorder_subtrees: "sorted_less (inorder (Node ts t)) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  using sorted_inorder_list_subtrees sorted_wrt_append by auto

lemma sorted_inorder_list_induct_subtree:
  "sorted_less (inorder_list (ls@(sub,sep)#rs)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

corollary sorted_inorder_induct_subtree:
  "sorted_less (inorder (Node (ls@(sub,sep)#rs) t)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_induct_last: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder t)"
  by (simp add: sorted_wrt_append)

end