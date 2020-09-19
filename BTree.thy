theory BTree                 
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Tree23_Set" "HOL-Data_Structures.Tree234_Set"
begin

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
(* definition heavily based on Tree234_Set, Pair structure from ...*)
(* TODO should all basic definitions be more abstract and use later refinements for implementations *)
(* TODO to keep the list as pairs, the type for the btrees should be changed to linorder with TOP
 alternative: sep is the element *smaller* than all all elements in the respective tree - problem: how to descend into the correct subtree?
 *)


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
fun seperators where "seperators xs = (map snd xs)"

definition btree_set:: "'a btree \<Rightarrow> 'a set" where 
  "btree_set = set \<circ> inorder"

fun btree_set_alt:: "'a btree \<Rightarrow> 'a set" where
"btree_set_alt Leaf = {}" |
"btree_set_alt (Node t) = set (seperators t) \<union> \<Union> (set (map (btree_set_alt) (subtrees t)))"



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
fun btree_list_choose:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> ('a btree\<times>'a) list \<Rightarrow>  (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
"btree_list_choose [] x prev = (prev, [])" |
"btree_list_choose ((sub, sep)#xs) x prev = (if x > sep then btree_list_choose xs x (prev @ [(sub, sep)]) else (prev, (sub,sep)#xs))"

lemma [simp]:"(x, (a, b) # x22) = btree_list_choose t y xs \<Longrightarrow>
       y \<noteq> b \<Longrightarrow> size a < Suc (size_list (\<lambda>x. Suc (size (fst x))) t)"
  apply(induction t y xs arbitrary: a b x x22 rule: btree_list_choose.induct)
  apply(simp_all)
  by (metis add_Suc_right less_SucI less_add_Suc1 list.inject old.prod.inject trans_less_add2)

fun isin:: "('a::linorder) btree \<Rightarrow> 'a \<Rightarrow> bool" where
 "isin (Leaf) y = False" |
 "isin (Node t) y = (case btree_list_choose t y [] of (_,r) \<Rightarrow> (case r of [] \<Rightarrow> False | (sub,sep)#xs \<Rightarrow> (if y = sep then True else isin sub y)))"


value "btree_set (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
(* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"


lemma child_subset: "p \<in> set t \<Longrightarrow> btree_set (fst p) \<subseteq> btree_set (Node t)"
  apply(induction p arbitrary: t)
   apply(auto simp add: btree_set_def append_foldr_set)
  done


lemma some_child_pair: 
 "btree_list_choose t y xs = (l,(sub,sep)#ts) \<Longrightarrow> (sub,sep) \<in> set t"
  apply(induction t y xs arbitrary: l sub sep ts rule: btree_list_choose.induct)
   apply(simp_all)
  by (metis Pair_inject list.inject)

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
  and "sep \<in> set (seperators t)"
  using assms by force+ 

lemma some_child_sm: "btree_list_choose t y xs = (l,(sub,sep)#ts) \<Longrightarrow> y \<le> sep"
  apply(induction t y xs arbitrary: l sub sep ts rule: btree_list_choose.induct)
  apply(simp_all)
  by (metis Pair_inject le_less_linear list.inject)


lemma isin_true_not_empty_r: "\<lbrakk>isin (Node t) y; btree_list_choose t y [] = (l, r)\<rbrakk> \<Longrightarrow> r \<noteq> []"
  unfolding isin.simps by auto


lemma isin_implied_in_set: "isin n y \<Longrightarrow> y \<in> btree_set n"
proof(induction n y rule: isin.induct)
  case (2 t y)
  then obtain l r where 21: "btree_list_choose t y [] = (l,r)" by auto
  then have "r \<noteq> []" using isin_true_not_empty_r 2 by auto
  then obtain sub sep xs where 22: "r = (sub,sep)#xs" by (cases r) auto
  then have "y = sep \<or> y \<noteq> sep" using 21 22 by blast
  then show ?case
  proof
    assume "y = sep"
    then have "y \<in> set (seperators t)" using some_child_sub(2) some_child_pair 2 21 22
      by metis
    then show "y \<in> btree_set (Node t)" by (simp add: btree_set_set_def)
  next
    assume "y \<noteq> sep"
    then have "y \<in> btree_set sub" unfolding btree_list_choose.simps using 2 21 22 by auto
    then show "y \<in> btree_set (Node t)"
      using "21" "22" child_subset some_child_pair by fastforce
  qed
qed simp

(* idea: make sorted_list a sorted_wrt *)
find_theorems sorted_wrt
thm sorted_wrt_append

fun sub_sep_sm where
 "sub_sep_sm (sub_l, sep_l) (sub_r, sep_r) =
  ((sep_l < sep_r) \<and> (\<forall>x \<in> btree_set sub_r. sep_l < x))"

fun sub_sep_cons where
"sub_sep_cons (sub, sep) = (\<forall>x \<in> btree_set sub. x < sep)"

lemma sorted_wrt_list_sorted: "sorted_wrt sub_sep_sm xs \<Longrightarrow> sorted (seperators xs)"
  apply(induction xs) 
   apply (auto simp add: sorted_wrt_Cons)
  done

lemma sorted_wrt_sorted_left: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> t \<in> set (subtrees xs) \<Longrightarrow> \<forall>x \<in> btree_set t. x > sep"
  apply(induction xs) 
   apply (auto simp add: sorted_wrt_Cons)
  done

(* the below is independent of the inter-pair sorting *)
lemma sorted_wrt_sorted_right: "\<forall>x \<in> set xs. sub_sep_cons x \<Longrightarrow> (t, sep) \<in> set xs \<Longrightarrow> \<forall>x \<in> btree_set t. x < sep"
  by auto

fun sorted_alt2 where
"sorted_alt2 Leaf = True" |
"sorted_alt2 (Node xs) = (sorted_wrt sub_sep_sm xs \<and> (\<forall>x \<in> set xs. sub_sep_cons x) \<and> (\<forall>sub \<in> set (subtrees xs). sorted_alt2 sub))"

value "sorted_alt (Node [(Node [(Node [], a\<^sub>1)], a\<^sub>2)])"
value "sorted (inorder (Node [(Node [(Node [], a\<^sub>1)], a\<^sub>2)]))"
value "sorted_alt2 (Node [(Node [(Node [], a\<^sub>1)], a\<^sub>2)])"

lemma "(sorted (inorder sub) \<and> (\<forall>x \<in> btree_set sub. x < sep)) = sorted((inorder sub) @ [sep])"
  unfolding btree_set_def using sorted_snoc_iff
  by auto


(* idea: we show that if any element is in the btree_set of a tree, then it must be in the list or in the subtree given by btree_list_choose,
show the latter by case distinction on the compare of btree_list *)

lemma btree_set_alt_induct: "x \<in> btree_set_alt (Node xs) \<Longrightarrow> x \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). x \<in> btree_set_alt sub)"
  apply(induction xs)
   apply(auto)
  done

find_theorems sorted_wrt map

lemma "btree_list_choose xs p ys = (l,r) \<Longrightarrow> l@r = ys@xs"
  apply(induction xs p ys arbitrary: l r rule: btree_list_choose.induct)
   apply(simp_all)
  apply(metis Pair_inject)
  done

lemma "\<lbrakk>btree_list_choose xs p ys = (l,r); sorted (seperators xs)\<rbrakk> \<Longrightarrow> \<forall>(sub,sep) \<in> set l. p > sep"
  

(* idea: our only requirement for btree_list_choose are the following two*)
(*TODO make btree_list_choose return the matching pair and the list left and right as well*)
lemma btree_list_choose_req:
  assumes  "btree_list_choose xs p [] = (l,r)"
    and "sorted (seperators xs)"
  shows "l @ r = xs"
  and "\<forall>(sub,sep) \<in> set l. p > sep"
  and "(case r of [] \<Rightarrow> True | ((psub,psep)#xs) \<Rightarrow> psep \<le> y \<and> (\<forall>(sub,sep) \<in> set xs. sep > y))"
  sorry

  


lemma isin_set: "sorted_alt2 t \<Longrightarrow> x \<in> btree_set_alt t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 xs y)
  then have "y \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub)"
    using btree_set_alt_induct by simp
  then show ?case
  proof
    assume "y \<in> set (seperators xs)"
    then have "\<lbrakk>sorted_wrt sub_sep_sm xs; (\<forall>x \<in> set xs. sub_sep_cons x)\<rbrakk> \<Longrightarrow> btree_list_choose xs y = Match"
      using btree_list_choose_req1 by simp
    then show "BTree.isin (Node xs) y" using 2 by simp
  next
    assume asms: "(\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub)"
    then have "\<lbrakk>(\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub); sorted_wrt sub_sep_sm xs; (\<forall>x \<in> set xs. sub_sep_cons x)\<rbrakk> \<Longrightarrow> (\<exists>s. btree_list_choose xs y = Subtree s \<and> y \<in> btree_set_alt s)"
      using btree_list_choose_req2 by simp
    then show "BTree.isin (Node xs) y" using 2
      by (metis BTree.isin.simps(2) asms list_result.simps(9) some_child_sub sorted_alt2.simps(2))
  qed
qed auto

lemma "sorted_alt2 t \<Longrightarrow> isin t y = (y \<in> btree_set t)"
  using BTree.isin_set btree_set_set_def isin_implied_in_set by fastforce

lemma "sorted_alt2 t \<Longrightarrow> sorted (inorder t)"
proof(induction t)
  case (Node xs)
  then have "\<lbrakk>sorted_wrt sub_sep_sm xs; \<forall>x\<in> set xs. sub_sep_cons x\<rbrakk> \<Longrightarrow> sorted (inorder (Node xs))"
  proof (induction xs)
    case (Cons a xs)
    then obtain sub sep where pair_a: "a = (sub,sep)" by (cases a) simp
    then have "\<forall>x \<in> set (seperators xs). sep < x"
      by (metis list.simps(9) local.Cons(2) prod.sel(2) seperators.simps sorted_wrt_Cons sorted_wrt_list_sorted)
    from pair_a Cons have "\<forall>t \<in> set (subtrees xs). (\<forall>x \<in> btree_set t. sep < x)"
      by (simp add: sorted_wrt_sorted_left)
    have "\<forall>x \<in> set (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) xs) []). sep < x" 
    then show ?case sorry
  qed auto
  then show ?case using Node by auto
qed auto

find_theorems sorted_wrt "(@)"
thm sorted_wrt_append


end