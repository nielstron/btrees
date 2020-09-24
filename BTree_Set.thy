theory BTree_Set
imports BTree
begin


lemma subtree_smaller: "subr \<in> set (subtrees xs) \<Longrightarrow> 
      size subr < Suc (size_list (\<lambda>x. Suc (size (fst x))) xs)"
  apply(induction xs)
   apply(simp_all)
  using image_iff by fastforce

datatype 'a up_i = T_i "'a btree" | Up_i "'a btree" 'a "'a btree"

locale split_fun =
  fixes split_fun ::  "(('a::{linorder, top}) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)"
  (* idea: our only requirement for split_fun are the following two + the append requirement*)
  assumes split_fun_req:
   "\<lbrakk>split_fun xs p = (l,r)\<rbrakk> \<Longrightarrow> l @ r = xs"
   "\<lbrakk>split_fun xs p = (l,r); sorted (seperators xs)\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (seperators l). p > sep"
   "\<lbrakk>split_fun xs p = (l,r); sorted (seperators xs)\<rbrakk> \<Longrightarrow> (case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> (p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep)))"

begin


lemma split_fun_child: "(ls, a # rs) = split_fun xs y \<Longrightarrow>
       a \<in> set xs"
  by (metis in_set_conv_decomp split_fun_axioms split_fun_def)

lemma [termination_simp]:"(x, (a, b) # x22) = split_fun t y \<Longrightarrow>
      size a < Suc (size_list (\<lambda>x. Suc (size (fst x))) t)"
  using split_fun_child subtree_smaller some_child_sub(1) by metis

subsection "isin Function"

fun isin:: "('a::{linorder, top}) btree \<Rightarrow> 'a \<Rightarrow> bool" where
 "isin (Leaf) y = False" |
 "isin (Node t) y = (case split_fun t y of (_,r) \<Rightarrow> (case r of [] \<Rightarrow> False | (sub,sep)#xs \<Rightarrow> (if y = sep then True else isin sub y)))"


lemma isin_true_not_empty_r: "\<lbrakk>isin (Node t) y; split_fun t y = (l, r)\<rbrakk> \<Longrightarrow> r \<noteq> []"
  unfolding isin.simps by auto



find_theorems set_btree
find_theorems map snd
thm snd_conv snds.intros btree.set_intros

lemma isin_implied_in_set: "isin n y \<Longrightarrow> y \<in> set_btree n"
proof(induction n y rule: isin.induct)
  case (2 t y)
  then obtain l r where 21: "split_fun t y = (l,r)" by auto
  then have "r \<noteq> []" using isin_true_not_empty_r 2 by auto
  then obtain sub sep xs where 22: "r = (sub,sep)#xs" by (cases r) auto
  then have "y = sep \<or> y \<noteq> sep" using 21 22 by blast
  then show ?case
  proof
    assume "y = sep"
    then have "y \<in> set (seperators t)" using some_child_sub(2) split_fun_child 2 21 22
      by metis
    then show "y \<in> set_btree (Node t)"
      by (meson seperators_in_set subsetD)
  next
    assume "y \<noteq> sep"
    then have "y \<in> set_btree sub" unfolding isin.simps using 2 21 22 by auto
    then show "y \<in> set_btree (Node t)"
      by (metis "21" "22" child_subset fst_eqD split_fun_child subsetD)
  qed
qed simp


(* from the split_fun axioms, we may follow the isin requirements *)
lemma split_fun_seperator_match:
  assumes "sorted (seperators xs)" 
    and "y \<in> set (seperators xs)" 
    and "split_fun xs y = (l,r)"
  shows "snd (hd r) = y"
  and "r \<noteq> []"
proof -
  have "y \<in> set (seperators (l@r))" using assms split_fun_req(1) by blast
  also have "y \<notin> set (seperators l)"
    using assms(1) assms(3) split_fun_req(2) by blast
  ultimately have "y \<in> set (seperators r)"
    by simp
  then show "snd (hd r) = y"
  proof (cases r)
    case (Cons a list)
    then obtain psub psep where a_split: "a = (psub, psep)" by (cases a)
    then have "(\<forall>x \<in> set (seperators list). y < x)" using  split_fun_req(3)[of xs y l r] assms Cons by auto
    then have "y \<notin> set (seperators list)" by auto
    then have "y = psep" using \<open>y \<in> set (seperators r)\<close> Cons a_split by simp
    then show ?thesis using Cons a_split by auto
  qed simp
  from \<open>y \<in> set (seperators r)\<close> show "r \<noteq> []" by auto
qed

thm sorted_wrt_sorted_left

lemma linear_split_subtree_match:
  assumes "\<exists>sub \<in> set (subtrees xs). y \<in> set_btree sub"
  assumes "sorted_wrt sub_sep_sm xs"
  assumes "\<forall>x \<in> set xs. sub_sep_cons x"
  assumes "split_fun xs y = (l,r)"
  shows "y \<in> set_btree (fst (hd r))"
  and "r \<noteq> []"
proof -
  have "\<forall> (sub,sep) \<in> set l. y > sep"
    using assms(2) assms(4) split_fun_req(2) sorted_wrt_list_sorted by fastforce
  then have "\<forall> (sub, sep) \<in> set l. y \<notin> set_btree sub"
    by (metis (no_types, lifting) Un_iff assms(2) assms(3) assms(4) case_prodI2 not_less_iff_gr_or_eq set_append some_child_sub(2) sorted_wrt_list_sorted split_fun_req(1) split_fun_req(2) sub_sep_cons.simps)
  moreover have "\<exists>sub \<in> set (subtrees (l@r)). y \<in> set_btree sub"
    using assms(1) assms(4) split_fun_req(1) by blast
  ultimately have "\<exists>sub \<in> set (subtrees r). y \<in> set_btree sub" by auto
  then show "y \<in> set_btree (fst (hd r))"
  proof (cases r)
    case (Cons a list)
    then obtain psub psep where a_split: "a = (psub, psep)" by (cases a)
    then have "y \<le> psep" 
      using  split_fun_req(3)[of xs y l r] assms Cons sorted_wrt_list_sorted by fastforce
    moreover have "\<forall>t \<in> set (subtrees list). \<forall>x \<in> set_btree t. psep < x"
      using sorted_wrt_sorted_left a_split assms(2) assms(4) split_fun_req(1) local.Cons sorted_wrt_append sorted_wrt_list_sorted by blast
    ultimately have "\<forall>t \<in> set (subtrees list). y \<notin> set_btree t"
      using leD by blast
    then have "y \<in> set_btree psub"
      using \<open>\<exists>sub\<in>set (subtrees r). y \<in> set_btree sub\<close> a_split local.Cons by auto
    then show ?thesis
      by (simp add: a_split local.Cons)
  qed simp
  from \<open>\<exists>sub \<in> set (subtrees r). y \<in> set_btree sub\<close> show "r \<noteq> []" by auto
qed


lemma isin_set: "sorted_alt t \<Longrightarrow> x \<in> set_btree t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 xs y)
    obtain l r where choose_split: "split_fun xs y = (l,r)"
      by fastforce
  from 2 have "y \<in> set (seperators xs) \<or> (\<exists>sub \<in> set (subtrees xs). y \<in> set_btree sub)"
    by (meson set_btree_induct)
  then show ?case
  proof
    assume asm: "y \<in> set (seperators xs)"
    then have "snd (hd r) = y" "r \<noteq> []" using choose_split split_fun_seperator_match asm 2 sorted_wrt_list_sorted
      by (metis sorted_alt.simps(2))+
    then show "isin (Node xs) y" unfolding isin.simps
      using choose_split by (cases r) auto
  next
    assume asms: "(\<exists>sub \<in> set (subtrees xs). y \<in> set_btree sub)"
    then have "y \<in> set_btree (fst (hd r))" "r \<noteq> []"
      using choose_split linear_split_subtree_match
      by (metis "2.prems"(1) sorted_alt.simps(2))+
    moreover have "fst (hd r) \<in> set (subtrees xs)"
      using calculation(2) choose_split split_fun_req(1) by fastforce
    ultimately show "isin (Node xs) y" using 2 choose_split
      unfolding isin.simps by (cases r) (fastforce)+
  qed
qed auto

lemma "sorted_alt t \<Longrightarrow> isin t y = (y \<in> set_btree t)"
  using isin_set isin_implied_in_set by fastforce

subsection "insert Function"

(* ideas: split at median (that is the abstract idea of taking the middle element)
or use the fact of sortedness and just split the list in half *)
fun median where "median xs = top"

fun node_i:: "nat \<Rightarrow> (('a::{linorder,top}) btree \<times> 'a) list \<Rightarrow> 'a up_i" where
"node_i k xs = (
if length xs \<le> 2*k then T_i (Node xs)
else (
  case split_fun xs (median (seperators xs)) of (ls, (sub,sep)#rs) \<Rightarrow>
    Up_i (Node (ls@[(sub,top)])) sep (Node rs)
  )
)"

fun node_i2:: "nat \<Rightarrow> (('a::{linorder,top}) btree \<times> 'a) list \<Rightarrow> 'a up_i" where
"node_i2 k xs = (
if length xs \<le> 2*k then T_i (Node xs)
else (
  case drop k xs of (sub,sep)#rs \<Rightarrow>
    Up_i (Node ((take k xs)@[(sub,top)])) sep (Node rs)
  )
)"

fun ins where
"ins k x Leaf = (Up_i Leaf x Leaf)" |
"ins k x (Node xs) = (case split_fun xs x of 
 (ls,(sub,sep)#rs) \<Rightarrow> 
  (case ins k x sub of 
    Up_i l a r \<Rightarrow> node_i k (ls @ (l,a)#(r,sep)#rs) | 
    T_i a \<Rightarrow> node_i k (ls @ (a,sep) # rs)
  )
)"

end



(*TODO: at some point this better be replaced with something binary search like *)
(* split *)
fun linear_split_help:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> ('a btree\<times>'a) list \<Rightarrow>  (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
"linear_split_help [] x prev = (prev, [])" |
"linear_split_help ((sub, sep)#xs) x prev = (if sep < x then linear_split_help xs x (prev @ [(sub, sep)]) else (prev, (sub,sep)#xs))"

fun linear_split:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
"linear_split xs x = linear_split_help xs x []"


lemma some_child_sm: "linear_split_help t y xs = (l,(sub,sep)#ts) \<Longrightarrow> y \<le> sep"
  apply(induction t y xs arbitrary: l sub sep ts rule: linear_split_help.induct)
  apply(simp_all)
  by (metis Pair_inject le_less_linear list.inject)



lemma linear_split_append: "linear_split_help xs p ys = (l,r) \<Longrightarrow> l@r = ys@xs"
  apply(induction xs p ys arbitrary: l r rule: linear_split_help.induct)
   apply(simp_all)
  apply(metis Pair_inject)
  done

lemma linear_split_sm: "\<lbrakk>linear_split_help xs p ys = (l,r); sorted (seperators (ys@xs)); \<forall>sep \<in> set (seperators ys). p > sep\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (seperators l). p > sep"
  apply(induction xs p ys arbitrary: l r rule: linear_split_help.induct)
   apply(simp_all)
  by (metis prod.inject)+

value "linear_split [(Leaf, 2)] (1::nat)"

lemma linear_split_gr: "\<lbrakk>linear_split_help xs p ys = (l,r); sorted (seperators (ys@xs)); \<forall>(sub,sep) \<in> set ys. p > sep\<rbrakk> \<Longrightarrow> 
(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep))"
proof(induction xs p ys arbitrary: l r rule: linear_split_help.induct)
  case (2 sub sep xs x prev)
  then obtain l r where btree_choose_lr: "linear_split_help ((sub, sep)#xs) x prev = (l,r)" by auto
  then show ?case
  using 2 proof (cases r)
  case (Cons a list)
  then obtain psub psep where a_head: "a = (psub, psep)" by (cases a)
  then have 21: "x \<le> psep" using  btree_choose_lr Cons some_child_sm by blast
  moreover from 2 Cons have "\<forall>(sub,sep) \<in> set list. x < sep"
  proof -
    have "sorted (seperators (l@r))" using linear_split_append btree_choose_lr
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


lemma linear_split_req:
  assumes  "linear_split xs p = (l,r)"
    and "sorted (seperators xs)"
  shows "\<forall>sep \<in> set (seperators l). p > sep"
  and "(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> (p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep)))"
proof - 
  show "\<forall>sep \<in> set (seperators l). p > sep" using assms linear_split_sm by force
next
  show "(case r of [] \<Rightarrow> True | ((psub, psep)#rs) \<Rightarrow> (p \<le> psep \<and> (\<forall>sep \<in> set (seperators rs). p < sep)))"
    using assms linear_split_gr by force
qed

interpretation btree_linear_search: split_fun "linear_split"
  by (simp add: linear_split_req linear_split_append split_fun_def)



end