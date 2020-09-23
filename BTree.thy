theory BTree                 
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Tree23_Set" "HOL-Data_Structures.Tree234_Set"
begin

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
(* definition heavily based on Tree234_Set, Pair structure from popl10 (malecha)/mtps08*)
(* TODO should all basic definitions be more abstract and use later refinements for implementations *)
(* TODO to keep the list as pairs, the type for the btrees may be changed to linorder with TOP
 alternative: sep is the element *smaller* than all all elements in the respective tree - problem: how to descend into the correct subtree?
 *)


(* TODO more abstract idea: inside each Btree node is some abstract implementation of a sorted list (i.e. a BST),
   providing access to a function that returns the element with closest smaller key than a given key*)

datatype 'a btree = Leaf | Node "('a btree * 'a) list"

fun inorder :: "'a btree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node kvs) = (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) kvs) [])" 

class height =
fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: (type) height
begin

fun height_btree :: "'a btree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node kvs) = Suc (fold max (map (height \<circ> fst) kvs) 0)"

instance ..

end

(* not sure if required but appearently already present for coding equivalence *)
lemma set_eq_fold: "fold max xs n = Max (set (n#xs))"
  by (metis Max.set_eq_fold)

value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"

fun subtrees where "subtrees xs = (map fst xs)"
fun seperators where "seperators xs = (map snd xs)"

definition set_btree_inorder:: "'a btree \<Rightarrow> 'a set" where 
  "set_btree_inorder = set \<circ> inorder"

thm btree.simps
find_theorems set_btree
value "set_btree (Node [(Leaf, 1::nat)])"

lemma append_foldr_set: "set (foldr (@) xs []) = \<Union> (set (map set xs))"
  apply(induction xs)
   apply(auto)
  done

lemma set_btree_inorder_set_btree: "set_btree_inorder t = set_btree t"
  apply(induction t)
   apply(auto simp add: set_btree_inorder_def append_foldr_set)
  done

lemma child_subset: "p \<in> set t \<Longrightarrow> set_btree (fst p) \<subseteq> set_btree (Node t)"
  apply(induction p arbitrary: t)
   apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
  and "sep \<in> set (seperators t)"
  using assms by force+ 


(* idea: we show that if any element is in the set_btree_inorder of a tree, then it must be in the list or in the subtree given by btree_list_choose,
show the latter by case distinction on the compare of btree_list *)

lemma set_btree_induct: "x \<in> set_btree (Node xs) \<Longrightarrow> x \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). x \<in> set_btree sub)"
  by (induction xs) auto


lemma seperators_in_set: "set (seperators t) \<subseteq> set_btree (Node t)"
  by (induction t) auto

lemma subtrees_in_set: "s \<in> set (subtrees t) \<Longrightarrow> set_btree s \<subseteq> set_btree (Node t)"
  by (induction t) auto


fun bal:: "'a btree \<Rightarrow> bool" where
"bal Leaf = True" |
"bal (Node t) = ((\<forall>sub \<in> set (subtrees t). height (Node t) = Suc (height sub)) \<and> (\<forall>sub \<in> set (subtrees t). bal sub))"

fun k_spread:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
"k_spread k Leaf = True" |
"k_spread k (Node t) = ((length t \<ge> k \<and> length t \<le> 2*k+1) \<and> (\<forall>sub \<in> set (subtrees t). k_spread k sub))"


value "set_btree_inorder (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
(* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"




(* idea: make sorted_list a sorted_wrt *)
find_theorems sorted_wrt
thm sorted_wrt_append

fun sub_sep_sm where
 "sub_sep_sm (sub_l, sep_l) (sub_r, sep_r) =
  ((sep_l < sep_r) \<and> (\<forall>x \<in> set_btree sub_r. sep_l < x))"

fun sub_sep_cons where
"sub_sep_cons (sub, sep) = (\<forall>x \<in> set_btree sub. x < sep)"

fun sorted_alt where
"sorted_alt Leaf = True" |
"sorted_alt (Node xs) = (sorted_wrt sub_sep_sm xs \<and> (\<forall>x \<in> set xs. sub_sep_cons x) \<and> (\<forall>sub \<in> set (subtrees xs). sorted_alt sub))"

value "sorted (inorder (Node [(Node [(Node [], a\<^sub>1)], a\<^sub>2)]))"
value "sorted_alt (Node [(Node [(Node [], a\<^sub>1)], a\<^sub>2)])"


lemma sorted_wrt_list_sorted: "sorted_wrt sub_sep_sm xs \<Longrightarrow> sorted (seperators xs)"
  by (induction xs) (auto simp add: sorted_wrt_Cons)

lemma sorted_wrt_sorted_left: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> t \<in> set (subtrees xs) \<Longrightarrow> \<forall>x \<in> set_btree t. x > sep"
  by (induction xs) (auto simp add: sorted_wrt_Cons)

(* the below is independent of the inter-pair sorting *)
lemma sorted_wrt_sorted_right: "\<forall>x \<in> set xs. sub_sep_cons x \<Longrightarrow> (t, sep) \<in> set xs \<Longrightarrow> \<forall>x \<in> set_btree t. x < sep"
  by auto

lemma sorted_pair_list: "(sorted (inorder sub) \<and> (\<forall>x \<in> set_btree_inorder sub. x < sep)) = sorted((inorder sub) @ [sep])"
  unfolding set_btree_inorder_def using sorted_snoc_iff
  by auto

find_theorems sorted_wrt map


find_theorems sorted_wrt "(@)"
find_theorems sorted_wrt "(#)"
thm sorted_wrt_append

lemma sorted_alt_sorted: "sorted_alt t \<Longrightarrow> sorted (inorder t)"
proof(induction t)
  case (Node xs)
  then have "\<lbrakk>sorted_alt (Node xs)\<rbrakk> \<Longrightarrow> sorted (inorder (Node xs))"
  proof (induction xs)
    case (Cons a list)
    then have Cons_help: 
      "sorted_wrt sub_sep_sm list" 
      "\<forall>x \<in> set list. sub_sep_cons x"
      "\<forall>sub \<in> set (subtrees list). sorted_alt sub"
      by (simp add: sorted_wrt_Cons)+
    then have "sorted_alt (Node list)" using Cons
      by simp
    then have Cons_sorted: "sorted (inorder (Node list))"
      using Cons.IH Cons.prems(2) by auto

    from Cons obtain sub sep where pair_a: "a = (sub,sep)" by (cases a) simp
    then have "sorted_alt sub" using Node Cons
      by simp
    then have "sorted (inorder sub)" using Node Cons pair_a
      by force

    from pair_a have "\<forall>x \<in> set (seperators list). sep < x"
      using sorted_wrt_Cons sorted_wrt_list_sorted Cons_help
      by (metis (no_types, lifting) Cons.prems(1) list.simps(9) seperators.simps snd_conv sorted_alt.simps(2))
    also from pair_a Cons have "\<forall>t \<in> set (subtrees list). (\<forall>x \<in> set_btree t. sep < x)"
      using sorted_alt.simps(2) sorted_wrt_sorted_left by blast
    ultimately have "\<forall>x \<in> set_btree (Node list). sep < x"
      by fastforce
    then have "\<forall>x \<in> set_btree_inorder (Node list). sep < x"
      by (simp add: set_btree_inorder_set_btree)
    then have sep_sm: "\<forall>x \<in> set (inorder (Node list)). sep < x"
      unfolding set_btree_inorder_def by auto
    then have "sorted (sep # inorder (Node list))"
      using Cons sorted_Cons_iff Cons_sorted by blast
    moreover have "\<forall>y \<in> set (inorder sub). \<forall>x \<in> set (inorder (Node list)). y < x"
      using Cons_help sep_sm pair_a Cons
      by (metis comp_apply dual_order.strict_trans list.set_intros(1) set_btree_inorder_def set_btree_inorder_set_btree sorted_alt.simps(2) sub_sep_cons.simps)
    ultimately have "sorted (inorder sub @ sep # inorder (Node list))"
      using sorted_wrt_append[of "(<)" "inorder sub" "sep # inorder (Node list)"] \<open>sorted (inorder (Node list))\<close>
      by (metis Cons.prems(1) \<open>Sorted_Less.sorted (BTree.inorder sub)\<close> list.set_intros(1) pair_a set_btree_inorder_set_btree sorted_alt.simps(2) sorted_mid_iff sorted_pair_list sub_sep_cons.simps)
    then have "sorted ((inorder sub @ [sep]) @ inorder (Node list))"
      by simp
    then have "sorted ((\<lambda>(sub, sep). BTree.inorder sub @ [sep]) a @ foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) list) [])"
      unfolding inorder.simps by (simp add: pair_a)
    then have "sorted (foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) (a#list)) [])" 
      by simp
    then show ?case by simp
  qed auto
  then show ?case using Node by auto
qed auto

lemma sorted_inorder_subtrees: "sorted (inorder (Node xs)) \<Longrightarrow> \<forall>x \<in> set (subtrees xs). sorted (inorder x)"
  apply(induction xs)
  apply(auto)
  using sorted_wrt_append apply blast
  by (metis fst_eqD sorted_cons sorted_mid_iff)

lemma sorted_inorder_subcons: "sorted (inorder (Node xs)) \<Longrightarrow> \<forall>x \<in> set xs. sub_sep_cons x"
  apply(induction xs)
   apply(auto)
   apply (metis set_btree_inorder_set_btree sorted_mid_iff sorted_pair_list)
  using sorted_cons sorted_mid_iff sorted_wrt_sorted_right by blast

lemma sorted_inorder_subsepsm: "sorted (inorder (Node xs)) \<Longrightarrow> sorted_wrt sub_sep_sm xs"
proof (induction xs)
  case (Cons x list)
  then obtain sub sep where x_pair: "x = (sub, sep)" by (cases x)
  then have list_split: "inorder (Node (x#list)) = inorder sub @ sep # inorder (Node list)" unfolding inorder.simps by auto
  then have "sorted (inorder (Node list))" 
    using sorted_wrt_append Cons.prems sorted_cons by fastforce
  then have sorted_wrt_rec: "sorted_wrt sub_sep_sm list" using Cons by auto

  from list_split have "\<forall>l \<in> set (inorder (Node list)). sep < l"
    by (metis Cons.prems sorted_Cons_iff sorted_wrt_append)
  then have "\<forall>l \<in> set_btree_inorder (Node list). sep < l"
    by (simp add: set_btree_inorder_def)
  then have "\<forall>l \<in> set_btree (Node list). sep < l"
    by (simp add: set_btree_inorder_set_btree)
  then have sorted_wrt_local: "\<forall>(sub_r, sep_r) \<in> set list. (sep < sep_r \<and> (\<forall>r \<in> set_btree sub_r. sep < r))"
    by auto
    
  from sorted_wrt_local sorted_wrt_rec show ?case
    unfolding sorted_wrt.simps sub_sep_sm.simps
    using x_pair by auto
qed auto
  

find_theorems sorted inorder

lemma sorted_sorted_alt: "sorted (inorder t) \<Longrightarrow> sorted_alt t"
proof(induction t)
  case (Node xs)
  then have "\<forall>x \<in> set (subtrees xs). sorted_alt x"
    using sorted_inorder_subtrees by fastforce
  moreover have "\<forall>x \<in> set xs. sub_sep_cons x"
    using Node(2) sorted_inorder_subcons by blast
  moreover have "sorted_wrt sub_sep_sm xs"
    using Node.prems sorted_inorder_subsepsm by blast
  ultimately show ?case using Node by auto
qed auto

lemma sorted_alt_eq: "sorted (inorder t) = sorted_alt t"
  using sorted_alt_sorted sorted_sorted_alt by blast


end