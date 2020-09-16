theory BTree                 
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Tree23_Set" "HOL-Data_Structures.Tree234_Set"
begin

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
(* definition heavily based on Tree234_Set, Pair structure from ...*)
(* TODO should all basic definitions be more abstract and use later refinements for implementations *)
(* TODO to keep the list as pairs, the type for the btrees should be changed to linorder with TOP *)


(* TODO more abstract idea: inside each Btree node is some abstract implementation of a sorted list (i.e. a BST),
   providing access to a function that returns the element with closest smaller key than a given key*)

datatype 'a btree = Leaf | Node "('a btree * 'a) list"

definition "btree_of_pair = fst"
definition "sep_of_pair = snd"

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
lemma set_eq_fold:"Suc (fold max xs 0) = Suc (Max (set (0#xs)))"
  by (metis Max.set_eq_fold)

value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"

fun subtrees where "subtrees xs = (map fst xs)"
fun seperators where "seperators xs = (map fst xs)"

definition btree_set:: "'a btree \<Rightarrow> 'a set" where 
  "btree_set = set \<circ> inorder"

fun btree_set_alt:: "'a btree \<Rightarrow> 'a set" where
"btree_set_alt Leaf = {}" |
"btree_set_alt (Node t) = set (map snd t) \<union> \<Union> (set (map (btree_set_alt) (subtrees t)))"



lemma append_foldr_set: "set (foldr (@) xs []) = \<Union> (set (map set xs))"
  apply(induction xs)
   apply(auto)
  done

lemma btree_set_set_def: "btree_set t = btree_set_alt t"
  apply(induction t)
   apply(auto simp add: btree_set_def append_foldr_set)
  by (metis image_eqI snd_conv)

fun bal:: "'a btree \<Rightarrow> bool" where
"bal Leaf = True" |
"bal (Node t) = ((\<forall>sub \<in> set (subtrees t). bal sub) \<and> (\<exists>h.\<forall>sub \<in> set (subtrees t). h = height sub))"


definition ordered:: "('a::linorder) btree \<Rightarrow> bool" where "ordered = sorted \<circ> inorder"

fun k_spread:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
"k_spread k Leaf = True" |
"k_spread k (Node t) = ((length t \<ge> k \<and> length t \<le> 2*k+1) \<and> (\<forall>sub \<in> set (subtrees t). k_spread k sub))"

datatype 'a list_result = Nomatch | Subtree "'a btree" | Match

(*TODO: at some point this better be replaced with something binary search like *)
fun btree_list_choose:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> 'a list_result" where
"btree_list_choose [] x = Nomatch" |
"btree_list_choose ((sub, sep)#xs) x = (case cmp x sep of LT \<Rightarrow> Subtree sub | EQ \<Rightarrow> Match | GT \<Rightarrow> btree_list_choose xs x)"


(* the following is what Isabelle requires *)
lemma [simp]: "btree_list_choose t y = Subtree x2 \<Longrightarrow>
       size x2 < Suc (size_list (\<lambda>x. Suc (size (fst x))) t)"
  apply (induction t)
  apply (auto split: list_result.splits)
  apply (metis (no_types, lifting) dual_order.strict_trans less_Suc_eq less_add_Suc1 list_result.distinct(5) list_result.inject not_add_less2 not_less_eq)
  done


fun isin:: "('a::linorder) btree \<Rightarrow> 'a \<Rightarrow> bool" where
 "isin (Leaf) y = False" |
 "isin (Node t) y = (case btree_list_choose t y of Nomatch \<Rightarrow> False | Match \<Rightarrow> True | Subtree sub \<Rightarrow> isin sub y)"


value "btree_set (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
(* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"


lemma child_subset: "p \<in> set t \<Longrightarrow> btree_set (fst p) \<subseteq> btree_set (Node t)"
  apply(induction p arbitrary: t)
   apply(auto simp add: btree_set_def append_foldr_set)
  done


lemma some_child_sub: "btree_list_choose t y = Subtree x \<Longrightarrow> x \<in> set (map fst t)"
  apply(induction t y rule: btree_list_choose.induct)
   apply(simp_all)
  by (metis GT list_result.distinct(5) list_result.inject)

lemma some_child_match: "btree_list_choose t y = Match \<Longrightarrow> y \<in> set (map snd t)"
  apply(induction t y rule: btree_list_choose.induct)
   apply(auto simp add: cmp_def)
  by (metis list_result.distinct(6))

lemma isin_true_not_nomatch: "isin (Node t) y = True \<Longrightarrow> btree_list_choose t y \<noteq> Nomatch"
  by auto


lemma "isin n y = True \<Longrightarrow> y \<in> btree_set n"
proof(induction n y rule: isin.induct)
  case (2 t y) 
  then have "btree_list_choose t y = Match \<or> (\<exists>sub. btree_list_choose t y = Subtree sub)"
    using isin_true_not_nomatch list_result.exhaust by blast
  then show ?case
  proof
    assume "btree_list_choose t y = Match"
    then show "y \<in> btree_set (Node t)" using some_child_match btree_set_set_def
      by (metis UnCI btree_set_alt.simps(2))
  next
    assume "\<exists>sub. btree_list_choose t y = Subtree sub"
    then obtain sub where sub_tree: "btree_list_choose t y = Subtree sub" by blast
    then have "sub \<in> set (map fst t)" using some_child_sub by auto
    also have "y \<in> btree_set sub" using 2 sub_tree by auto
    ultimately show "y \<in> btree_set (Node t)" 
      using child_subset by fastforce
  qed
qed simp

fun sorted_list:: "('a::{linorder, bot}) \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> bool" where
"sorted_list left [] = True" |
"sorted_list left ((sub, sep)#xs) = ((\<forall>x \<in> btree_set sub. x > left \<and> x < sep) \<and> left < sep \<and> sorted_list sep xs)"

fun sorted_alt:: "('a::{linorder, bot} btree) \<Rightarrow> bool" where
"sorted_alt Leaf = True" |
"sorted_alt (Node xs) = (sorted_list bot xs \<and> (\<forall>sub \<in> set (map fst xs). sorted_alt sub))"

lemma sorted_list_part: "sorted_list a xs \<Longrightarrow> sorted (map snd ((t, a)#xs))"
  apply(induction a xs rule: sorted_list.induct)
   apply(auto)
  done
  

lemma sorted_list_bot: "sorted_list bot xs \<Longrightarrow> sorted (map snd xs)"
  using sorted_list_part by (cases xs) auto


lemma "sorted (inorder t) = sorted_alt t"
  apply(induction t)
   apply(auto) 
sorry

lemma isin_set: "sorted(inorder t) \<Longrightarrow> isin t x = (x \<in> btree_set t)"
  unfolding btree_set_def 
  apply (induction t) 
   apply(auto split: list_result.splits) 
  sorry

end