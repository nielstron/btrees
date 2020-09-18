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


lemma some_child_sub: "btree_list_choose t y = Subtree x \<Longrightarrow> x \<in> set (subtrees t)"
  apply(induction t y rule: btree_list_choose.induct)
   apply(simp_all)
  by (metis GT list_result.distinct(5) list_result.inject)

lemma some_child_match: "btree_list_choose t y = Match \<Longrightarrow> y \<in> set (seperators t)"
  apply(induction t y rule: btree_list_choose.induct)
   apply(auto simp add: cmp_def)
  by (metis list_result.distinct(6))

lemma isin_true_not_nomatch: "isin (Node t) y = True \<Longrightarrow> btree_list_choose t y \<noteq> Nomatch"
  by auto


lemma isin_implied_in_set: "isin n y \<Longrightarrow> y \<in> btree_set n"
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
    then have "sub \<in> set (subtrees t)" using some_child_sub by auto
    also have "y \<in> btree_set sub" using 2 sub_tree by auto
    ultimately show "y \<in> btree_set (Node t)" 
      using child_subset by fastforce
  qed
qed simp

fun sorted_list_help:: "('a::{linorder}) \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> bool" where
"sorted_list_help left [] = True" |
"sorted_list_help left ((sub, sep)#xs) = ((\<forall>x \<in> btree_set sub. x > left \<and> x < sep) \<and> left < sep \<and> sorted_list_help sep xs)"

fun sorted_list:: "(('a::linorder) btree \<times> 'a) list \<Rightarrow> bool" where
"sorted_list [] = True" |
"sorted_list ((sub, sep)#xs) = ((\<forall>x \<in> btree_set sub. x < sep) \<and> sorted_list_help sep xs)"


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

lemma isin_set: "sorted_alt2 t \<Longrightarrow> x \<in> btree_set_alt t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 xs y)
  from 2 have tmp: "sorted_wrt sub_sep_sm xs" by auto
  from 2 have tmp2: "\<forall>x \<in> set xs. sub_sep_cons x" by auto
  
  from 2 have "y \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub)"
    using btree_set_alt_induct by simp
  then show ?case
  proof
    assume "y \<in> set (seperators xs)"
    then have "\<lbrakk>sorted_wrt sub_sep_sm xs; (\<forall>x \<in> set xs. sub_sep_cons x)\<rbrakk> \<Longrightarrow> btree_list_choose xs y = Match"
    proof (induction xs y rule: btree_list_choose.induct)
      case (2 sub sep ys y)
      then show ?case
      using 2 proof (cases "cmp y sep")
        case LT
        from 2 have "sorted (seperators ((sub,sep)#ys))" using sorted_wrt_list_sorted by blast
        then have "sorted (sep#(seperators ys))" by simp
        then have "\<forall>x \<in> set (seperators ys). sep < x"
          by (simp add: sorted_wrt_Cons)
        then have "y \<notin> set (seperators ys)"
          using local.LT by auto
        then have "y \<notin> set (seperators ((sub, sep) # ys))"
          using local.LT by auto
        then show ?thesis
          using "2.prems"(3) by auto
      next
        case GT
        (* we need to show that sortedness is inductive *)
        from 2 have "sorted_wrt sub_sep_sm ys"
          by (simp add: sorted_wrt_Cons)
        then show ?thesis using GT 2 sorted_wrt_Cons by auto
      qed auto
    qed auto
    then show "BTree.isin (Node xs) y" using 2 by simp
  next
    assume "(\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub)"
    then have "\<lbrakk>(\<exists>sub \<in> set (subtrees xs). y \<in> btree_set_alt sub); sorted_wrt sub_sep_sm xs; (\<forall>x \<in> set xs. sub_sep_cons x)\<rbrakk> \<Longrightarrow> (\<exists>s. btree_list_choose xs y = Subtree s \<and> y \<in> btree_set_alt s)"
    proof (induction xs y rule: btree_list_choose.induct)
      case (2 sub sep ys y)
      then show ?case
      using 2 proof (cases "cmp y sep")
        case LT

        from 2 have "t \<in> set (subtrees ys) \<Longrightarrow> \<forall>x \<in> btree_set t. x > sep"
          using sorted_wrt_sorted_left by blast
        then have "t \<in> set (subtrees ys) \<Longrightarrow> \<forall>x \<in> btree_set t. x > y" using local.LT by auto
        then have "t \<in> set (subtrees ys) \<Longrightarrow> y \<notin> btree_set t" by auto
        then have y_not_in_subs: "t \<in> set (subtrees ys) \<Longrightarrow> y \<notin> btree_set_alt t" by (simp add: btree_set_set_def)

        from 2 have "\<exists>sub \<in> set (subtrees ((sub,sep)#ys)). y \<in> btree_set_alt sub" by simp
        then have "\<exists>sub \<in> set (sub#(subtrees ys)). y \<in> btree_set_alt sub" by simp
        then have "y \<in> btree_set_alt sub" 
          by (metis "2.prems"(2) GT btree_set_set_def cmp_val.distinct(3) local.LT set_ConsD sorted_wrt_sorted_left)
        then show ?thesis unfolding btree_list_choose.simps
          by (simp add: local.LT)
      next
        case GT
        (* we need to show that sortedness is inductive *)
        from 2 have GT1: "sorted_wrt sub_sep_sm ys"
          by (simp add: sorted_wrt_Cons)
        from 2 have GT2: "\<exists>t \<in> set (subtrees ys). y \<in> btree_set_alt t"
        proof - (* due to z3 *)
        obtain bb :: "'a btree" where
          f1: "bb \<in> set (subtrees ((sub, sep) # ys)) \<and> y \<in> btree_set_alt bb"
          using "2.prems"(1) by blast
        then have f2: "bb \<in> fst ` set ((sub, sep) # ys)"
          by simp
        obtain pp :: "('a btree \<times> 'a) set \<Rightarrow> ('a btree \<times> 'a \<Rightarrow> 'a btree) \<Rightarrow> 'a btree \<Rightarrow> 'a btree \<times> 'a" where
          "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (pp x0 x1 x2 \<in> x0 \<and> x2 = x1 (pp x0 x1 x2))"
          by moura
          then have "\<forall>b f P. (b \<notin> f ` P \<or> pp P f b \<in> P \<and> b = f (pp P f b)) \<and> (b \<in> f ` P \<or> (\<forall>p. p \<notin> P \<or> b \<noteq> f p))"
          by blast
        then have "bb \<in> fst ` set ys"
          using f2 f1 by (metis (no_types) "2.prems"(3) btree_set_set_def cmp_def cmp_val.distinct(3) fst_conv local.GT set_ConsD sub_sep_cons.simps)
          then show ?thesis
            using f1 by auto
        qed
        then show ?thesis using GT 2 sorted_wrt_Cons GT1 GT2 by simp
      next
        case EQ
        then show ?thesis
          using "2.prems"(1) "2.prems"(2) "2.prems"(3) btree_set_set_def sorted_wrt_sorted_left by fastforce
      qed
    qed auto
    then show "BTree.isin (Node xs) y" using 2
      by (metis BTree.isin.simps(2) \<open>\<exists>sub\<in>set (subtrees xs). y \<in> btree_set_alt sub\<close> list_result.simps(9) some_child_sub sorted_alt2.simps(2))
  qed
qed auto

lemma "sorted_alt2 t \<Longrightarrow> isin t y = (y \<in> btree_set t)"
  using BTree.isin_set btree_set_set_def isin_implied_in_set by fastforce

lemma "sorted_alt2 t = sorted (inorder t)"
  sorry (*TODO*)

end