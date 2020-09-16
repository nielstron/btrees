theory BTree                 
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Tree234_Set"
begin

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
(* definition heavily based on Tree234_Set, Pair structure from ...*)

datatype btree = Leaf | Node "(btree * nat) list"

definition "btree_of_pair = fst"
definition "sep_of_pair = snd"

fun inorder :: "btree \<Rightarrow> nat list" where
"inorder Leaf = []" |
"inorder (Node kvs) = (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) kvs) [])" 

class height =
fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: height
begin

fun height_btree :: "btree \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node kvs) = Suc (fold max (map (height \<circ> fst) kvs) 0)"

instance ..

end

(* not sure if required but appearently already present for coding equivalence *)
lemma set_eq_fold:"Suc (fold max xs 0) = Suc (Max (set (0#xs)))"
  by (metis Max.set_eq_fold)

value "(Node [(Leaf, 1), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"
value "inorder (Node [(Leaf, 1), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"

fun children where
"children Leaf = {}" |
"children (Node xs) = (set (map fst xs))"

definition btree_set:: "btree \<Rightarrow> nat set" where 
  "btree_set = set \<circ> inorder"

fun btree_list:: "(btree * nat) list \<Rightarrow> bool" where
 "btree_list [] = True" |
 "btree_list ((sub, sep)#xs) = (\<forall>x \<in> btree_set sub. x < sep \<and> btree_list xs )"


definition "length_invar k xs = (length xs \<ge> k \<and> length xs \<le> 2*k+1)"
definition "key_invar xs = (sorted (map snd xs))"

fun k_btree:: "nat \<Rightarrow> btree \<Rightarrow> bool"  where
 "k_btree k Leaf = True"
| "k_btree k (Node xs) = (length_invar k xs \<and> key_invar xs \<and> btree_list xs \<and> (fold (\<and>) (map (k_btree k \<circ> fst) xs) True))"

fun k_btree_root where
"k_btree_root k Leaf = True" |
"k_btree_root k (Node xs) = (key_invar xs \<and> btree_list xs \<and>  (fold (\<and>) (map (k_btree k \<circ> btree_of_pair) xs) True))"

datatype list_result = Nomatch | Subtree btree | Match

fun btree_list_choose where
"btree_list_choose x [] = Nomatch" |
"btree_list_choose x ((sub, sep)#xs) = (case cmp x sep of LT \<Rightarrow> Subtree sub | EQ \<Rightarrow> Match | GT \<Rightarrow> btree_list_choose x xs)"

(* the following is what Isabelle requires *)
lemma [simp]: "btree_list_choose y t = Subtree x2 \<Longrightarrow>
       size x2 < Suc (size_list (\<lambda>x. Suc (size (fst x))) t)"
  apply (induction t)
  apply (auto split: list_result.splits)
  apply (metis (no_types, lifting) dual_order.strict_trans less_Suc_eq less_add_Suc1 list_result.distinct(5) list_result.inject not_add_less2 not_less_eq)
  done

fun isin where
 "isin y (Leaf) = False" |
 "isin y (Node t) = (case btree_list_choose y t of Nomatch \<Rightarrow> False | Match \<Rightarrow> True | Subtree sub \<Rightarrow> isin y sub)"


value "btree_set (Node [(Leaf, 0), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
value "height (Node [(Leaf, 0), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
(* a bit weird *)
value "size (Node [(Leaf, 0), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"


lemma append_foldr_set: "set (foldr (@) xs []) = \<Union> (set (map set xs))"
  apply(induction xs)
   apply(auto)
  done

lemma child_subset: "p \<in> set t \<Longrightarrow> btree_set (fst p) \<subseteq> btree_set (Node t)"
  apply(induction p arbitrary: t)
   apply(auto simp add: btree_set_def append_foldr_set)
  done


lemma some_child_sub: "btree_list_choose y t = Subtree x \<Longrightarrow> x \<in> set (map fst t)"
  apply(induction y t rule: btree_list_choose.induct)
   apply(simp_all)
  by (metis GT list_result.distinct(5) list_result.inject)

lemma some_child_match: "btree_list_choose y t = Match \<Longrightarrow> y \<in> set (map snd t)"
  apply(induction y t rule: btree_list_choose.induct)
   apply(auto simp add: cmp_def)
  by (metis list_result.distinct(6))

lemma "isin y t = True \<Longrightarrow> y \<in> btree_set t"
proof(induction y t rule: isin.induct)
  case (1 y)
  then show ?case by simp
next
  case (2 y t)
then show ?case sorry
qed


end