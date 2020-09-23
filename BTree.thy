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
lemma set_eq_fold:"fold max xs n = Max (set (n#xs))"
  by (metis Max.set_eq_fold)

value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)], 10), (Leaf, 30), (Leaf, 100)])"

fun subtrees where "subtrees xs = (map fst xs)"
fun seperators where "seperators xs = (map snd xs)"

definition btree_set:: "'a btree \<Rightarrow> 'a set" where 
  "btree_set = set \<circ> inorder"

thm btree.simps
(* TODO use set_btree instead *)
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


(*TODO: at some point this better be replaced with something binary search like *)
(* split *)
fun btree_list_choose_help:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> ('a btree\<times>'a) list \<Rightarrow>  (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
"btree_list_choose_help [] x prev = (prev, [])" |
"btree_list_choose_help ((sub, sep)#xs) x prev = (if sep < x then btree_list_choose_help xs x (prev @ [(sub, sep)]) else (prev, (sub,sep)#xs))"

fun btree_list_choose:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
"btree_list_choose xs x = btree_list_choose_help xs x []"


lemma [termination_simp]:"(x, (a, b) # x22) = btree_list_choose_help t y xs \<Longrightarrow>
       y \<noteq> b \<Longrightarrow> size a < Suc (size_list (\<lambda>x. Suc (size (fst x))) t)"
  apply(induction t y xs arbitrary: a b x x22 rule: btree_list_choose_help.induct)
  apply(simp_all)
  by (metis add_Suc_right less_SucI less_add_Suc1 list.inject old.prod.inject trans_less_add2)

fun isin:: "('a::linorder) btree \<Rightarrow> 'a \<Rightarrow> bool" where
 "isin (Leaf) y = False" |
 "isin (Node t) y = (case btree_list_choose t y of (_,r) \<Rightarrow> (case r of [] \<Rightarrow> False | (sub,sep)#xs \<Rightarrow> (if y = sep then True else isin sub y)))"


value "btree_set (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"
(* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)], 12), (Leaf, 30), (Leaf, 100)])"


lemma child_subset: "p \<in> set t \<Longrightarrow> btree_set (fst p) \<subseteq> btree_set (Node t)"
  apply(induction p arbitrary: t)
   apply(auto simp add: btree_set_def append_foldr_set)
  done


lemma some_child_pair: 
 "btree_list_choose_help t y xs = (l,(sub,sep)#ts) \<Longrightarrow> (sub,sep) \<in> set t"
  apply(induction t y xs arbitrary: l sub sep ts rule: btree_list_choose_help.induct)
   apply(simp_all)
  by (metis Pair_inject list.inject)

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
  and "sep \<in> set (seperators t)"
  using assms by force+ 

lemma some_child_sm: "btree_list_choose_help t y xs = (l,(sub,sep)#ts) \<Longrightarrow> y \<le> sep"
  apply(induction t y xs arbitrary: l sub sep ts rule: btree_list_choose_help.induct)
  apply(simp_all)
  by (metis Pair_inject le_less_linear list.inject)


lemma isin_true_not_empty_r: "\<lbrakk>isin (Node t) y; btree_list_choose_help t y [] = (l, r)\<rbrakk> \<Longrightarrow> r \<noteq> []"
  unfolding isin.simps by auto


lemma isin_implied_in_set: "isin n y \<Longrightarrow> y \<in> btree_set n"
proof(induction n y rule: isin.induct)
  case (2 t y)
  then obtain l r where 21: "btree_list_choose_help t y [] = (l,r)" by auto
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

lemma btree_list_choose_append: "btree_list_choose_help xs p ys = (l,r) \<Longrightarrow> l@r = ys@xs"
  apply(induction xs p ys arbitrary: l r rule: btree_list_choose_help.induct)
   apply(simp_all)
  apply(metis Pair_inject)
  done

lemma btree_list_choose_sm: "\<lbrakk>btree_list_choose_help xs p ys = (l,r); sorted (seperators (ys@xs)); \<forall>sep \<in> set (seperators ys). p > sep\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (seperators l). p > sep"
  apply(induction xs p ys arbitrary: l r rule: btree_list_choose_help.induct)
   apply(simp_all)
  by (metis prod.inject)+

value "btree_list_choose [(Leaf, 2)] (1::nat)"
find_theorems sorted_wrt "(@)"

lemma btree_list_choose_gr: "\<lbrakk>btree_list_choose_help xs p ys = (l,r); sorted (seperators (ys@xs)); \<forall>(sub,sep) \<in> set ys. p > sep\<rbrakk> \<Longrightarrow> 
(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep))"
proof(induction xs p ys arbitrary: l r rule: btree_list_choose_help.induct)
  case (2 sub sep xs x prev)
  then obtain l r where btree_choose_lr: "btree_list_choose_help ((sub, sep)#xs) x prev = (l,r)" by auto
  then show ?case
  using 2 proof (cases r)
  case (Cons a list)
  then obtain psub psep where a_head: "a = (psub, psep)" by (cases a)
  then have 21: "x \<le> psep" using  btree_choose_lr Cons some_child_sm by blast
  also from 2 Cons have "\<forall>(sub,sep) \<in> set list. x < sep"
  proof -
    have "sorted (seperators (l@r))" using btree_list_choose_append btree_choose_lr
      by (metis "2.prems"(2))
    then have "sorted ((seperators l)@(seperators r))" by simp
    then have "sorted (seperators r)" using sorted_wrt_append by auto
    then have "sorted (seperators ((psub,psep)#list))" using a_head Cons by blast
    then have "sorted (psep#(seperators list))" by auto
    then have "\<forall>(sub,sep) \<in> set list. sep > psep"
      by (metis case_prodI2 some_child_sub(2) sorted_wrt_Cons)
    then show ?thesis
      using calculation by auto
  qed
    ultimately show ?thesis
      using "2.prems"(1) \<open>a = (psub, psep)\<close> btree_choose_lr local.Cons by auto 
  qed simp
qed simp

    



(* idea: our only requirement for btree_list_choose are the following two*)
(*TODO make btree_list_choose return the matching pair and the list left and right as well*)
lemma btree_list_choose_req:
  assumes  "btree_list_choose xs p = (l,r)"
    and "sorted (seperators xs)"
  shows "l @ r = xs"
  and "\<forall>sep \<in> set (seperators l). p > sep"
  and "(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> (p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep)))"
proof - 
  show "l@r = xs"
    using assms(1) btree_list_choose_append by force
next
  show "\<forall>sep \<in> set (seperators l). p > sep" using assms btree_list_choose_sm by force
next
  show "(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> (p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep)))"
    using assms btree_list_choose_gr by force
qed

  

(* from the above simple requirements, we may follow the isin requirements (hopefully) *)
lemma btree_list_choose_seperator_match:
  assumes "sorted (seperators xs)" 
    and "y \<in> set (seperators xs)" 
    and "btree_list_choose xs y = (l,r)"
  shows "snd (hd r) = y"
  and "r \<noteq> []"
proof -
  have "y \<in> set (seperators (l@r))" using btree_list_choose_req(1) assms by blast
  also have "y \<notin> set (seperators l)"
    using assms(1) assms(3) btree_list_choose_req(2) by blast
  ultimately have "y \<in> set (seperators r)"
    by simp
  then show "snd (hd r) = y"
  proof (cases r)
    case (Cons a list)
    then obtain psub psep where a_split: "a = (psub, psep)" by (cases a)
    then have "(\<forall>x \<in> set (seperators list). y < x)" using  btree_list_choose_req(3)[of xs y l r] assms Cons by auto
    then have "y \<notin> set (seperators list)" by auto
    then have "y = psep" using \<open>y \<in> set (seperators r)\<close> Cons a_split by simp
    then show ?thesis using Cons a_split by auto
  qed simp
  from \<open>y \<in> set (seperators r)\<close> show "r \<noteq> []" by auto
qed

thm sorted_wrt_sorted_left

lemma btree_list_choose_subtree_match:
  assumes "\<exists>sub \<in> set (subtrees xs). y \<in> btree_set sub"
  assumes "sorted_wrt sub_sep_sm xs"
  assumes "\<forall>x \<in> set xs. sub_sep_cons x"
  assumes "btree_list_choose xs y = (l,r)"
  shows "y \<in> btree_set (fst (hd r))"
  and "r \<noteq> []"
proof -
  have "\<forall> (sub,sep) \<in> set l. y > sep"
    using assms(2) assms(4) btree_list_choose_req(2) sorted_wrt_list_sorted by fastforce
  then have "\<forall> (sub, sep) \<in> set l. y \<notin> btree_set sub"
    by (metis (no_types, lifting) Un_iff assms(2) assms(3) assms(4) btree_list_choose_req(1) btree_list_choose_req(2) btree_set_set_def case_prodI2 less_asym' set_append some_child_sub(2) sorted_wrt_list_sorted sub_sep_cons.simps)
  moreover have "\<exists>sub \<in> set (subtrees (l@r)). y \<in> btree_set sub"
    using assms(1) assms(2) assms(4) btree_list_choose_req(1) sorted_wrt_list_sorted by blast
  ultimately have "\<exists>sub \<in> set (subtrees r). y \<in> btree_set sub" by auto
  then show "y \<in> btree_set (fst (hd r))"
  proof (cases r)
    case (Cons a list)
    then obtain psub psep where a_split: "a = (psub, psep)" by (cases a)
    then have "y \<le> psep" 
      using  btree_list_choose_req(3)[of xs y l r] assms Cons sorted_wrt_list_sorted by fastforce
    moreover have "\<forall>t \<in> set (subtrees list). \<forall>x \<in> btree_set t. psep < x"
      using sorted_wrt_sorted_left a_split assms(2) assms(4) btree_list_choose_req(1) local.Cons sorted_wrt_append sorted_wrt_list_sorted by blast
    ultimately have "\<forall>t \<in> set (subtrees list). y \<notin> btree_set t"
      using leD by blast
    then have "y \<in> btree_set psub"
      using \<open>\<exists>sub\<in>set (subtrees r). y \<in> btree_set sub\<close> a_split local.Cons by auto
    then show ?thesis
      by (simp add: a_split local.Cons)
  qed simp
  from \<open>\<exists>sub \<in> set (subtrees r). y \<in> btree_set sub\<close> show "r \<noteq> []" by auto
qed

thm btree_list_choose_subtree_match

lemma isin_set: "sorted_alt2 t \<Longrightarrow> x \<in> btree_set t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 xs y)
    obtain l r where choose_split: "btree_list_choose xs y = (l,r)"
      by fastforce
  from 2 have "y \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). y \<in> btree_set sub)"
    using btree_set_alt_induct by (simp add: btree_set_set_def)
  then show ?case
  proof
    assume asm: "y \<in> set (seperators xs)"
    then have "snd (hd r) = y" "r \<noteq> []" using choose_split btree_list_choose_seperator_match asm 2 sorted_wrt_list_sorted
      by (metis sorted_alt2.simps(2))+
    then show "BTree.isin (Node xs) y" unfolding isin.simps
      using choose_split by (cases r) auto
  next
    assume asms: "(\<exists>sub \<in> set (subtrees xs). y \<in> btree_set sub)"
    then have "y \<in> btree_set (fst (hd r))" "r \<noteq> []"
      using choose_split btree_list_choose_subtree_match
      by (metis "2.prems"(1) sorted_alt2.simps(2))+
    moreover have "fst (hd r) \<in> set (subtrees xs)"
      by (metis (no_types, lifting) btree_list_choose.elims calculation(2) choose_split eq_fst_iff list.sel(1) list.set_cases list.set_sel(1) some_child_pair some_child_sub(1))
    ultimately show "BTree.isin (Node xs) y" using 2 choose_split
      unfolding isin.simps by (cases r) (fastforce)+
  qed
qed (auto simp add: btree_set_set_def)

lemma "sorted_alt2 t \<Longrightarrow> isin t y = (y \<in> btree_set t)"
  using BTree.isin_set btree_set_set_def isin_implied_in_set by fastforce

lemma "\<lbrakk>\<forall>y \<in> set ys. \<forall>x \<in> set xs. y < x; sorted ys; sorted xs\<rbrakk> \<Longrightarrow> sorted (ys@xs)"
  using sorted_wrt_append by blast


find_theorems sorted_wrt "(@)"
find_theorems sorted_wrt "(#)"
thm sorted_wrt_append

lemma "sorted_alt2 t \<Longrightarrow> sorted (inorder t)"
proof(induction t)
  case (Node xs)
  then have "\<lbrakk>sorted_alt2 (Node xs)\<rbrakk> \<Longrightarrow> sorted (inorder (Node xs))"
  proof (induction xs)
    case (Cons a list)
    then have Cons_help: 
      "sorted_wrt sub_sep_sm list" 
      "\<forall>x \<in> set list. sub_sep_cons x"
      "\<forall>sub \<in> set (subtrees list). sorted_alt2 sub"
      by (simp add: sorted_wrt_Cons)+
    then have "sorted_alt2 (Node list)" using Cons
      by simp
    then have Cons_sorted: "sorted (inorder (Node list))"
      using Cons.IH Cons.prems(2) by auto

    from Cons obtain sub sep where pair_a: "a = (sub,sep)" by (cases a) simp
    then have "sorted_alt2 sub" using Node Cons
      by simp
    then have "sorted (inorder sub)" using Node Cons pair_a
      by force

    from pair_a have "\<forall>x \<in> set (seperators list). sep < x"
      using sorted_wrt_Cons sorted_wrt_list_sorted Cons_help
      by (metis (no_types, lifting) Cons.prems(1) list.simps(9) seperators.simps snd_conv sorted_alt2.simps(2))
    also from pair_a Cons have "\<forall>t \<in> set (subtrees list). (\<forall>x \<in> btree_set t. sep < x)"
      using sorted_alt2.simps(2) sorted_wrt_sorted_left by blast
    ultimately have "\<forall>x \<in> btree_set_alt (Node list). sep < x"
      using btree_set_set_def by fastforce
    then have "\<forall>x \<in> btree_set (Node list). sep < x"
      by (simp add: btree_set_set_def)
    then have sep_sm: "\<forall>x \<in> set (inorder (Node list)). sep < x"
      unfolding btree_set_def by auto
    then have "sorted (sep # inorder (Node list))"
      using Cons sorted_Cons_iff Cons_sorted by blast
    moreover have "\<forall>y \<in> set (inorder sub). \<forall>x \<in> set (inorder (Node list)). y < x"
      using Cons_help sep_sm pair_a Cons
      by (metis (no_types, lifting) btree_set_def comp_apply dual_order.strict_trans list.set_intros(1) sorted_alt2.simps(2) sub_sep_cons.simps)
    ultimately have "sorted (inorder sub @ sep # inorder (Node list))"
      using sorted_wrt_append[of "(<)" "inorder sub" "sep # inorder (Node list)"] \<open>sorted (inorder (Node list))\<close>
      by (metis \<open>Sorted_Less.sorted (BTree.inorder sub)\<close> btree_set_def comp_apply insert_iff list.set(2) local.Cons(2) pair_a sorted_alt2.simps(2) sub_sep_cons.simps)
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

lemma "sorted (inorder t) \<Longrightarrow> sorted_alt2 t"
proof(induction t)
  case (Node xs)
  then have "\<lbrakk>sorted (inorder (Node xs))\<rbrakk> \<Longrightarrow> sorted_alt2 (Node xs)"
  proof (induction xs)
    case (Cons a list)
      show ?case sorry
  qed auto
  then show ?case using Node by auto
qed auto



end