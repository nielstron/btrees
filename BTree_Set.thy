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
  fixes split_fun ::  "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)"
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
      size a < Suc (size_list (\<lambda>x. Suc (size (fst x))) t  + size l)"
  using split_fun_child subtree_smaller some_child_sub(1)
  by fastforce

subsection "isin Function"

fun isin:: "('a::linorder) btree \<Rightarrow> 'a \<Rightarrow> bool" where
 "isin (Leaf) y = False" |
 "isin (Node t l) y = (case split_fun t y of (_,r) \<Rightarrow> (case r of (sub,sep)#_ \<Rightarrow> (if y = sep then True else isin sub y) | [] \<Rightarrow> isin l y))"


lemma isin_true_not_empty_r: "\<lbrakk>isin (Node ts t) y; split_fun ts y = (l, r)\<rbrakk> \<Longrightarrow> r \<noteq> [] \<or> (r=[] \<and> isin t y)"
  unfolding isin.simps by auto



find_theorems set_btree
find_theorems map snd
thm snd_conv snds.intros btree.set_intros

lemma isin_implied_in_set: "isin n y \<Longrightarrow> y \<in> set_btree n"
proof(induction n y rule: isin.induct)
  case (2 ts t y)
  then obtain l r where 21: "split_fun ts y = (l,r)" by auto
  then have "r \<noteq> [] \<or> (r = [] \<and> isin t y)" using isin_true_not_empty_r 2 by auto
  then show ?case
  proof
    assume "r \<noteq> []"
    then obtain sub sep xs where 22: "r = (sub,sep)#xs" by (cases r) auto
    then have "y = sep \<or> y \<noteq> sep" using 21 22 by blast
    then show "y \<in> set_btree (Node ts t)"
    proof
      assume "y = sep"
      then have "y \<in> set (seperators ts)" using some_child_sub(2) split_fun_child 2 21 22
        by metis
      then show "y \<in> set_btree (Node ts t)"
        by (meson seperators_in_set subsetD)
    next
      assume "y \<noteq> sep"
      then have "y \<in> set_btree sub" unfolding isin.simps using 2 21 22 by auto
      then show "y \<in> set_btree (Node ts t)"
        by (metis "21" "22" child_subset fst_eqD split_fun_child subsetD)
    qed
  next
    assume "r = [] \<and> isin t y"
    then have "y \<in> set_btree t" 
      by (simp add: "2.IH"(1) "21")
    then show "y \<in> set_btree (Node ts t)" unfolding btree.set by auto
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

lemma split_fun_subtree_match:
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

(* Additional proof for last tree *)
lemma split_fun_last_empty: 
  assumes "y \<in> set_btree t"
    and "(\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree t. sep < y)"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "sorted (seperators ts)"
    and "split_fun ts y = (l,r)"
  shows "r = []"
proof (cases r)
  case Nil
  then show ?thesis by simp
next
  case (Cons a list)
  then obtain sub sep where a_pair: "a = (sub,sep)" by (cases a)
  then have "y \<le> sep" 
    using assms split_fun_def split_fun_axioms Cons a_pair by fastforce
  then have "False"
    by (metis a_pair assms(1) assms(2) assms(5) leD local.Cons some_child_sub(2) split_fun_child)
  then show ?thesis by simp
qed
  

lemma isin_set: "sorted_alt t \<Longrightarrow> x \<in> set_btree t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 ts t y)
    obtain l r where choose_split: "split_fun ts y = (l,r)"
      by fastforce
  from 2 have "y \<in> set (seperators ts) \<or> (\<exists>sub \<in> set (subtrees ts). y \<in> set_btree sub) \<or> y \<in> set_btree t"
    by (meson set_btree_induct)
  then show ?case
  proof (elim disjE)
    assume asm: "y \<in> set (seperators ts)"
    then have "snd (hd r) = y" "r \<noteq> []" using choose_split split_fun_seperator_match asm 2 sorted_wrt_list_sorted
      by (metis sorted_alt.simps(2))+
    then show "isin (Node ts t) y" unfolding isin.simps
      using choose_split by (cases r) auto
  next
    assume asms: "(\<exists>sub \<in> set (subtrees ts). y \<in> set_btree sub)"
    then have "y \<in> set_btree (fst (hd r))" "r \<noteq> []"
      using choose_split split_fun_subtree_match
      by (metis "2.prems"(1) sorted_alt.simps(2))+
    moreover have "fst (hd r) \<in> set (subtrees ts)"
      using calculation(2) choose_split split_fun_req(1) by fastforce
    ultimately show "isin (Node ts t) y" using 2 choose_split
      unfolding isin.simps by (cases r) (fastforce)+
  next
    assume asms: "y \<in> set_btree t"
    then have "r = []" 
      using split_fun_last_empty "2.prems"(1) choose_split
      using sorted_alt.simps(2) sorted_wrt_list_sorted by blast
    then show "isin (Node ts t) y"
      unfolding isin.simps 
      using "2.IH"(1) "2.prems"(1) asms choose_split by auto
  qed
qed auto

lemma "sorted_alt t \<Longrightarrow> isin t y = (y \<in> set_btree t)"
  using isin_set isin_implied_in_set by fastforce

subsection "insert Function"

fun tree_i where
"tree_i (T_i sub) = sub" |
"tree_i (Up_i l a r) = (Node [(l,a)] r)"

fun node_i:: "nat \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> 'a btree \<Rightarrow> 'a up_i" where
"node_i k xs x = (
if length xs \<le> 2*k then T_i (Node xs x)
else (
  case drop (length xs div 2) xs of (sub,sep)#rs \<Rightarrow>
    Up_i (Node (take (length xs div 2) xs) sub) sep (Node rs x)
  )
)"

find_theorems drop length take
thm append_take_drop_id

fun inorder_i where
"inorder_i (T_i sub) = inorder sub" |
"inorder_i (Up_i l a r) = (inorder l @ [a]) @ inorder r"

lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto)
  done


fun ins where
"ins k x Leaf = (Up_i Leaf x Leaf)" |
"ins k x (Node ts t) = (case split_fun ts x of
 (ls,(sub,sep)#rs) \<Rightarrow> 
  (case ins k x sub of 
    Up_i l a r \<Rightarrow> node_i k (ls @ (l,a)#(r,sep)#rs) t | 
    T_i a \<Rightarrow> T_i (Node (ls @ (a,sep) # rs) t)
  ) |
 (ls, []) \<Rightarrow>
  (case ins k x t of
    Up_i l a r \<Rightarrow> node_i k (ls@[(l,a)]) r |
    T_i a \<Rightarrow> T_i (Node ls a)
  )
)"

fun order_i where
"order_i k (T_i sub) = order k sub" |
"order_i k (Up_i l a r) = (order k l \<and> order k r)"

lemma node_i_order_i:
  assumes "length ts \<ge> k"
    and "length ts \<le> 2*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "order_i k (node_i k ts t)"
proof (cases "length ts \<le> 2*k")
case True
  then show ?thesis using set_map_pred_eq assms by simp
next
  case False
  then have length_ts: "length ts = 2*k+1"
    using assms(2) by linarith
  then have "drop (length ts div 2) ts \<noteq> []" by simp
  then obtain sub sep rs where drop_ts: "drop (length ts div 2) ts = (sub,sep)#rs" 
    by (metis eq_snd_iff hd_Cons_tl)
  then have "length rs = length ts - (length ts div 2) - 1" using length_drop
    by (metis One_nat_def add_diff_cancel_right' list.size(4))
  then have "length rs \<ge> k" "length rs \<le> 2*k" using length_ts
    by (simp_all)
  moreover have "set ((sub,sep)#rs) \<subseteq> set ts"
    by (metis drop_ts set_drop_subset)
  ultimately have o_r: "order k sub" "order k (Node rs t)" using drop_ts assms drop_ts by auto
  moreover have "length (take (length ts div 2) ts) \<ge> k" "length (take (length ts div 2) ts) \<le> 2*k"
    using length_take assms length_ts by(simp_all)
  ultimately have o_l: "order k (Node (take (length ts div 2) ts) sub)"
    using set_take_subset assms by fastforce
  from o_r o_l have "order_i k (Up_i (Node (take (length ts div 2) ts) sub) sep (Node rs t))" by simp
  then show ?thesis unfolding node_i.simps
    by (simp add: False drop_ts)
qed

find_theorems "set" "(@)" "(#)"

lemma "order k t \<Longrightarrow> order_i k (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce

  from 2 have suborders:
    "order k t"
    "\<forall>s \<in> set (subtrees ts). order k s"
    "length ts \<le> 2*k"
    "length ts \<ge> k"
    unfolding order.simps by simp+
  then have "\<forall>x \<in> set (subtrees l). order k x" using suborders split_app
    by auto
  
  show ?case
  proof (cases r)
    case Nil
    then have "order_i k (ins k x t)" using 2 suborders split_res
      by simp
    
    show ?thesis
    proof (cases "ins k x t")
      case (T_i x1)
      then have "order k x1"
        using \<open>order_i k (local.ins k x t)\<close> by auto
      moreover have "length l \<le> 2*k" "length l \<ge> k" using suborders split_app Nil
        by auto
      moreover have "\<forall>x \<in> set (subtrees l). order k x" using suborders split_app Nil
        by simp
      ultimately have "order k (Node l x1)"
        using order.simps(2) by blast
      then show ?thesis unfolding ins.simps using T_i Nil 2 split_res
        by simp
    next
      case (Up_i x21 x22 x23)
      then have "order k x21" "order k x23"
        using \<open>order_i k (local.ins k x t)\<close> by auto
      moreover have "length (l@[(x21,x22)]) \<le> 2*k+1" "length (l@[(x21,x22)]) \<ge> k" using suborders split_app Nil
        by auto
      moreover have "\<forall>x \<in> set (subtrees (l@[(x21,x22)])). order k x" using \<open>order k x21\<close> suborders split_app Nil
        by auto
      ultimately have "order_i k (node_i k (l@[(x21,x22)]) x23)"
        using node_i_order_i by (simp del: node_i.simps)
      then show ?thesis  unfolding ins.simps using Up_i Nil 2 split_res
        by simp
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then have "order_i k (ins k x sub)" using 2 suborders split_res
      by (metis local.Cons some_child_sub(1) split_fun_child)
    
    show ?thesis
    proof (cases "ins k x sub")
      case (T_i x1)
      then have "order k t"
        using 2 by auto
      moreover have "length  (l @ (x1,sep) # list) \<le> 2*k" "length (l @ (sub,sep) # list) \<ge> k"
        using suborders split_app Cons
        by auto
      moreover have "\<forall>x \<in> set (subtrees l). order k x" "order k x1" "\<forall>x \<in> set (subtrees list). order k x"
        using suborders split_app Cons T_i  \<open>order_i k (local.ins k x sub)\<close>
        by auto
      ultimately have "order k (Node (l @ (x1,sep) # list) t)"
        by auto
      then show ?thesis unfolding ins.simps using T_i Cons 2 split_res a_prod
        by simp
    next
      case (Up_i x21 x22 x23)
      then have "order k t"
        using 2 by auto
      moreover have
        "length (l@(x21,x22)#(x23,sep)#list) \<le> 2*k+1"
        "length (l@(x21,x22)#(x23,sep)#list) \<ge> k"
        using suborders split_app Cons by auto
      moreover have "\<forall>x \<in> set (subtrees l). order k x" "\<forall>x \<in> set (subtrees list). order k x"
        using suborders split_app Cons by auto
      moreover have "order k x21" "order k x23"
        using \<open>order_i k (local.ins k x sub)\<close> Up_i by auto
      ultimately have "order_i k (node_i k (l@(x21,x22)#(x23,sep)#list) t)"
        using node_i_order_i[of k "(l@(x21,x22)#(x23,sep)#list)" t]
        by (auto simp del: node_i.simps)
      then show ?thesis  unfolding ins.simps using Up_i Cons 2 split_res a_prod
        by simp
    qed
  qed
qed simp



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