theory BTree                 
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Tree234_Set"
begin

declare sorted_wrt.simps(2)[simp add]

subsection "General structure and concepts definition"

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
(* definition heavily based on Tree234_Set, Pair structure from popl10 (malecha)/mtps08*)
(* TODO should all basic definitions be more abstract and use later refinements for implementations *)
(* TODO to keep the list as pairs, the type for the btrees may be changed to linorder with TOP
 alternative: sep is the element *smaller* than all all elements in the respective tree - problem: how to descend into the correct subtree?
 *)


(* TODO more abstract idea: inside each Btree node is some abstract implementation of a sorted list (i.e. a BST),
   providing access to a function that returns the element with closest smaller key than a given key*)

datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

fun inorder :: "'a btree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node ts t) = (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) []) @ inorder t" 

fun subtrees where "subtrees xs = (map fst xs)"
fun seperators where "seperators xs = (map snd xs)"

class height =
fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: (type) height
begin

fun height_btree :: "'a btree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node ts t) = Suc (fold max (map height (subtrees ts)) (height t))"

instance ..

end

(* not sure if required but appearently already present for coding equivalence *)
lemma set_eq_fold: "fold max xs n = Max (set xs \<union> {n})"
  by (metis Max.set_eq_fold Un_insert_right list.simps(15) sup_bot.right_neutral)

value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"


lemma set_map_pred_eq: "(\<forall>x \<in> set (map f xs). P x) = (\<forall>x \<in> set xs. P (f x))"
  apply(induction xs)
   apply(auto)
  done


definition set_btree_inorder:: "'a btree \<Rightarrow> 'a set" where 
  "set_btree_inorder = set \<circ> inorder"

thm btree.simps
find_theorems set_btree
value "set_btree (Node [(Leaf, 1::nat)] Leaf)"


lemma append_foldr_set: "set (foldr (@) xs []) = \<Union> (set (map set xs))"
  apply(induction xs)
   apply(auto)
  done

lemma set_btree_inorder_set_btree: "set_btree_inorder t = set_btree t"
  apply(induction t)
   apply(auto simp add: set_btree_inorder_def append_foldr_set)
  done

lemma child_subset: "p \<in> set t \<Longrightarrow> set_btree (fst p) \<subseteq> set_btree (Node t n)"
  apply(induction p arbitrary: t n)
   apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
  and "sep \<in> set (seperators t)"
  using assms by force+ 


(* idea: we show that if any element is in the set_btree_inorder of a tree, then it must be in the list or in the subtree given by btree_list_choose,
show the latter by case distinction on the compare of btree_list *)

lemma set_btree_induct: "x \<in> set_btree (Node ts t) \<Longrightarrow> x \<in> set (seperators ts) \<or> (\<exists>sub \<in> set (subtrees ts). x \<in> set_btree sub) \<or> x \<in> set_btree t"
  by (induction ts) auto


lemma seperators_in_set: "set (seperators ts) \<subseteq> set_btree (Node ts t)"
  by auto

lemma subtrees_in_set: "s \<in> set (subtrees ts) \<Longrightarrow> set_btree s \<subseteq> set_btree (Node ts t)"
  by auto


fun bal:: "'a btree \<Rightarrow> bool" where
"bal Leaf = True" |
"bal (Node ts t) = ((\<forall>sub \<in> set (subtrees ts). height t = height sub) \<and> (\<forall>sub \<in> set (subtrees ts). bal sub) \<and> bal t)"

lemma bal_all_subtrees_equal: "bal (Node ts t) \<Longrightarrow> (\<forall>s1 \<in> set (subtrees ts). \<forall>s2 \<in> set (subtrees ts). height s1 = height s2)"
  by (metis BTree.bal.simps(2))

find_theorems fold max

lemma fold_max_set: "\<forall>x \<in> set t. x = f \<Longrightarrow> fold max t f = f"
  apply(induction t)
   apply(auto simp add: max_def_raw)
  done

lemma height_bal_tree: "bal (Node ts t) \<Longrightarrow> height (Node ts t) = Suc (height t)"
  unfolding height_btree.simps bal.simps
  by (simp add: fold_max_set)

  

(*value "nat \<lceil>(5::nat) / 2\<rceil>"*)

(* alt1: following knuths definition to allow for any natural number as order and resolve ambiguity *)
(* alt2: use range [k,2*k] allowing for valid btrees from k=1 onwards *)
fun order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
"order k Leaf = True" |
"order k (Node ts t) = ((length ts \<ge> k  \<and> length ts \<le> 2*k) \<and> (\<forall>sub \<in> set (subtrees ts). order k sub) \<and> order k t)"


value "set_btree_inorder (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"
(* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"




(* idea: make sorted_list a sorted_wrt *)
find_theorems sorted_wrt
thm sorted_wrt_append

fun sub_sep_sm where
 "sub_sep_sm (sub_l, sep_l) (sub_r, sep_r) =
  ((sep_l < sep_r) \<and> (\<forall>x \<in> set_btree sub_r. sep_l < x))"

fun sub_sep_cons where
"sub_sep_cons (sub, sep) = (\<forall>x \<in> set_btree sub. x < sep)"

subsection "sortedness"

fun sorted_alt where
"sorted_alt Leaf = True" |
"sorted_alt (Node ts t) = (sorted_wrt sub_sep_sm ts \<and> (\<forall>x \<in> set ts. sub_sep_cons x) \<and> (\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree t. sep < y) \<and> (\<forall>sub \<in> set (subtrees ts). sorted_alt sub) \<and> sorted_alt t)"

value "sorted (inorder (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf))"
value "sorted_alt (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf)"


lemma sorted_wrt_list_sorted: "sorted_wrt sub_sep_sm xs \<Longrightarrow> sorted (seperators xs)"
  by (induction xs) (auto simp add: sorted_wrt_Cons)


lemma sorted_wrt_sorted_left: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> t \<in> set (subtrees xs) \<Longrightarrow> \<forall>x \<in> set_btree t. x > sep"
  by (induction xs) (auto simp add: sorted_wrt_Cons)

(* the below is independent of the inter-pair sorting *)
lemma sorted_wrt_sorted_right: "\<forall>x \<in> set xs. sub_sep_cons x \<Longrightarrow> (t, sep) \<in> set xs \<Longrightarrow> \<forall>x \<in> set_btree t. x < sep"
  by auto

find_theorems sorted_wrt "(@)"

(* this works only for linear orders *)
lemma sorted_wrt_sorted_right2: "
sorted_wrt sub_sep_sm (ls@(sub,(sep::('a::linorder)))#rs) \<Longrightarrow> (\<forall>x \<in> set (ls@(sub,sep)#rs). sub_sep_cons x) \<Longrightarrow>
 (\<forall>x \<in> set_btree (Node ls sub). x < sep)"
  apply (auto simp add: sorted_wrt_append)
  by (meson UnI1 dual_order.strict_trans sub_sep_cons.simps sub_sep_sm.simps)

lemma sorted_pair_list: "(sorted (inorder sub) \<and> (\<forall>x \<in> set_btree_inorder sub. x < sep)) = sorted((inorder sub) @ [sep])"
  unfolding set_btree_inorder_def using sorted_snoc_iff
  by auto

find_theorems sorted_wrt map


find_theorems sorted_wrt "(@)"
find_theorems sorted_wrt "(#)"
thm sorted_wrt_append

lemma sorted_alt_sorted: "sorted_alt t \<Longrightarrow> sorted (inorder t)"
proof(induction t)
  case (Node ts t)
  then have "\<lbrakk>sorted_alt (Node ts t)\<rbrakk> \<Longrightarrow> sorted (inorder (Node ts t))"
  proof (induction ts)
    case (Cons a list)
    then have Cons_help: 
      "sorted_wrt sub_sep_sm list" 
      "\<forall>x \<in> set list. sub_sep_cons x"
      "\<forall>sub \<in> set (subtrees list). sorted_alt sub"
      by (simp_all add: sorted_wrt_Cons)
    then have "sorted_alt (Node list t)" using Cons
      by simp
    then have Cons_sorted: "sorted (inorder (Node list t))"
      using Cons.IH Cons.prems(2) Node.IH(2) by auto

    from Cons obtain sub sep where pair_a: "a = (sub,sep)" by (cases a) simp
    then have "sorted_alt sub" using Node Cons
      by simp
    then have "sorted (inorder sub)" using Node Cons pair_a
      by force

    from pair_a have "\<forall>x \<in> set (seperators list). sep < x"
      using sorted_wrt_Cons sorted_wrt_list_sorted Cons_help
      by (metis (no_types, lifting) Cons.prems(1) list.simps(9) seperators.simps snd_conv sorted_alt.simps(2))
    also from pair_a Cons have "\<forall>t \<in> set (subtrees list). (\<forall>x \<in> set_btree t. sep < x)"
      using sorted_alt.simps(2) sorted_wrt_sorted_left by metis
    ultimately have "\<forall>x \<in> set_btree (Node list t). sep < x"
      using Cons.prems(1) pair_a by auto
    then have "\<forall>x \<in> set_btree_inorder (Node list t). sep < x"
      by (simp add: set_btree_inorder_set_btree)
    then have sep_sm: "\<forall>x \<in> set (inorder (Node list t)). sep < x"
      unfolding set_btree_inorder_def by auto
    then have "sorted (sep # inorder (Node list t))"
      using Cons_sorted sorted_Cons_iff by blast
    moreover have "\<forall>y \<in> set (inorder sub). \<forall>x \<in> set (inorder (Node list t)). y < x"
      using Cons_help sep_sm pair_a Cons
      by (metis comp_apply dual_order.strict_trans list.set_intros(1) set_btree_inorder_def set_btree_inorder_set_btree sorted_alt.simps(2) sub_sep_cons.simps)
    ultimately have "sorted (inorder sub @ sep # inorder (Node list t))"
      using sorted_wrt_append[of "(<)" "inorder sub" "sep # inorder (Node list t)"] \<open>sorted (inorder (Node list t))\<close>
      by (metis Cons.prems(1) \<open>Sorted_Less.sorted (BTree.inorder sub)\<close> list.set_intros(1) pair_a set_btree_inorder_set_btree sorted_alt.simps(2) sorted_mid_iff sorted_pair_list sub_sep_cons.simps)
    then have "sorted ((inorder sub @ [sep]) @ inorder (Node list t))"
      by simp
    then have "sorted ((\<lambda>(sub, sep). BTree.inorder sub @ [sep]) a @ foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) list) [] @ inorder t)"
      unfolding inorder.simps by (simp add: pair_a)
    then have "sorted (foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) (a#list)) [] @ inorder t)" 
      by simp
    then show ?case by simp
  qed auto
  then show ?case using Node by auto
qed auto

lemma sorted_inorder_subtrees: "sorted (inorder (Node ts t)) \<Longrightarrow> \<forall>x \<in> set (subtrees ts). sorted (inorder x)"
  apply(induction ts)
  apply(auto)
  using sorted_wrt_append apply blast
  by (metis fst_eqD sorted_cons sorted_mid_iff)

lemma sorted_inorder_last: "sorted (inorder (Node ts t)) \<Longrightarrow> sorted (inorder t)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_subcons: "sorted (inorder (Node ts t)) \<Longrightarrow> \<forall>x \<in> set ts. sub_sep_cons x"
  apply(induction ts)
   apply(auto)
   apply (metis set_btree_inorder_set_btree sorted_mid_iff sorted_pair_list)
  using sorted_cons sorted_mid_iff sorted_wrt_sorted_right by blast

lemma sorted_inorder_fold: "sorted (inorder (Node ts t)) \<Longrightarrow> (\<forall>x \<in> set (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) []). \<forall>y \<in> set_btree_inorder t. x < y)"
  apply(induction ts)
   apply (simp add: set_btree_inorder_def sorted_Cons_iff sorted_wrt_append)+
  by blast

lemma seperators_subset: "set (seperators xs) \<subseteq> set (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) xs) [])"
  apply(induction xs)
   apply(auto)
  done

lemma sorted_inorder_seps: "sorted (inorder (Node ts t)) \<Longrightarrow> (\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree_inorder t. sep < y)"
  using sorted_inorder_fold seperators_subset by fastforce
  

lemma sorted_inorder_subsepsm: "sorted (inorder (Node ts t)) \<Longrightarrow> sorted_wrt sub_sep_sm ts"
proof (induction ts)
  case (Cons x list)
  then obtain sub sep where x_pair: "x = (sub, sep)" by (cases x)
  then have list_split: "inorder (Node (x#list) t) = inorder sub @ sep # inorder (Node list t)" unfolding inorder.simps by auto
  then have "sorted (inorder (Node list t))" 
    using  Cons.prems sorted_cons
    by (simp add: list_split sorted_wrt_append sorted_wrt_Cons)
  then have sorted_wrt_rec: "sorted_wrt sub_sep_sm list" using Cons by auto

  from list_split have "\<forall>l \<in> set (inorder (Node list t)). sep < l"
    by (metis Cons.prems sorted_Cons_iff sorted_wrt_append)
  then have "\<forall>l \<in> set_btree_inorder (Node list t). sep < l"
    by (simp add: set_btree_inorder_def)
  then have "\<forall>l \<in> set_btree (Node list t). sep < l"
    by (simp add: set_btree_inorder_set_btree)
  then have sorted_wrt_local: "\<forall>(sub_r, sep_r) \<in> set list. (sep < sep_r \<and> (\<forall>r \<in> set_btree sub_r. sep < r))"
    by (induction list) auto 
    
  from sorted_wrt_local sorted_wrt_rec show ?case
    unfolding sorted_wrt.simps sub_sep_sm.simps
    using x_pair by auto
qed auto
  

find_theorems sorted inorder

lemma sorted_sorted_alt: "sorted (inorder t) \<Longrightarrow> sorted_alt t"
proof(induction t)
  case (Node ts t)
  then have "\<forall>x \<in> set (subtrees ts). sorted_alt x"
    using sorted_inorder_subtrees by fastforce
  moreover have "\<forall>x \<in> set ts. sub_sep_cons x"
    using Node.prems sorted_inorder_subcons by blast
  moreover have "sorted_wrt sub_sep_sm ts"
    using Node.prems sorted_inorder_subsepsm by blast
  moreover have "(\<forall>sep \<in> set (seperators ts). \<forall>lv \<in> set_btree t. sep < lv)"
    using Node.prems sorted_inorder_seps set_btree_inorder_set_btree by fastforce
  moreover have "sorted (inorder t)"
    using sorted_inorder_last Node.prems by blast
  ultimately show ?case using Node
    by simp
qed auto

lemma sorted_alt_eq: "sorted (inorder t) = sorted_alt t"
  using sorted_alt_sorted sorted_sorted_alt by blast


end