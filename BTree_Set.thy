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
  (if sep = x then
    T_i (Node ts t)
  else
    (case ins k x sub of 
      Up_i l a r \<Rightarrow> node_i k (ls @ (l,a)#(r,sep)#rs) t | 
      T_i a \<Rightarrow> T_i (Node (ls @ (a,sep) # rs) t))
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

lemma split_fun_length_l: "split_fun ts x = (l,[]) \<Longrightarrow> length l = length ts"
  using split_fun_req by fastforce

lemma split_fun_length: "split_fun ts x = (x1, (a, b) # x22) \<Longrightarrow> Suc(length x1 + length x22) = length ts"
  using split_fun_req by fastforce

lemma split_fun_set_l: "split_fun ts x = (l,[]) \<Longrightarrow> set l = set ts"
  using split_fun_req by fastforce

lemma split_fun_set: 
  assumes "split_fun ts z = (l,(a,b)#r)"
  shows "(a,b) \<in> set ts"
    and "(x,y) \<in> set l \<Longrightarrow> (x,y) \<in> set ts"
    and "(x,y) \<in> set r \<Longrightarrow> (x,y) \<in> set ts"
    and "set l \<union> set r \<union> {(a,b)} = set ts"
    and "\<exists>x \<in> set ts. b \<in> Basic_BNFs.snds x"
  using split_fun_req assms by fastforce+

lemma impl_one_two: "(\<exists>x \<in> set ts. b \<in> Basic_BNFs.snds x) \<Longrightarrow> \<exists>x\<in>set ts. ((\<exists>x\<in>Basic_BNFs.fsts x. b \<in> set_btree x) \<or> b \<in> Basic_BNFs.snds x)"
  by auto

thm fst_conv

lemma order_fst: "\<forall>x \<in> xs. P (fst x) \<Longrightarrow> (a,b) \<in> xs \<Longrightarrow> P a"
  by auto

lemma inductive_order: "\<lbrakk>
   \<forall>x\<in>set x1. order k (fst x);
   split_fun x1 x = (x1a, (a, b) # x22);
   local.ins k x a = T_i x1b;
   (\<And>a b x1aa. (a, b) \<in> set x1 \<Longrightarrow> x1aa = a \<Longrightarrow> order k a \<Longrightarrow> order_i k (local.ins k x a))
\<rbrakk> \<Longrightarrow> order k x1b"
  by (metis fst_conv order_i.simps(1) split_fun_child)

lemma length_help:
  assumes "k \<le> length x1"
    and "length x1 \<le> 2 * k"
    and "\<forall>x\<in>set x1. order k (fst x)"
    and "order k t"
    and "split_fun x1 x = (l, (sub, sep) # list)"
    and "local.ins k x sub = Up_i x21 x22 x23"
and "(\<And>a b x1aa. (a, b) \<in> set x1 \<Longrightarrow> x1aa = a \<Longrightarrow> order k a \<Longrightarrow> order_i k (local.ins k x a))"
shows "order_i k (node_i k (l @ (x21, x22) # (x23, sep) # list) t)"
proof -
  have "order k t"
    using assms by auto
  moreover have
    "length (l@(x21,x22)#(x23,sep)#list) \<le> 2*k+1"
    "length (l@(x21,x22)#(x23,sep)#list) \<ge> k"
    using split_fun_length assms by auto
  moreover have "\<forall>x \<in> set (subtrees l). order k x" "\<forall>x \<in> set (subtrees list). order k x"
    using assms split_fun_set by auto
  moreover have "order k x21" "order k x23"
    using assms split_fun_set(1) split_fun_axioms by fastforce+
  ultimately show "order_i k (node_i k (l@(x21,x22)#(x23,sep)#list) t)"
    using node_i_order_i[of k "(l@(x21,x22)#(x23,sep)#list)" t]
    by (auto simp del: node_i.simps simp add: split_fun_length split_fun_set assms)
qed
  
(* "Automatic proof", using a number of lemmata *)
lemma "order k t \<Longrightarrow> order_i k (ins k x t)"
  apply(induction t)
   apply(auto simp del: node_i.simps split!: prod.splits list.splits up_i.splits
 simp add: split_fun_length_l split_fun_length split_fun_set_l inductive_order split_fun_set node_i_order_i
length_help)
  done

(* direct proof *)
lemma "order k t \<Longrightarrow> order_i k (ins k x t)"
proof(induction t)
  case (Node ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce

  from Node have suborders:
    "order k t"
    "\<forall>s \<in> set (subtrees ts). order k s"
    "length ts \<le> 2*k"
    "length ts \<ge> k"
    unfolding order.simps by simp_all
  
  show ?case
  proof (cases r)
    case Nil
    then have "order_i k (ins k x t)" using Node suborders split_res
      by simp
    
    show ?thesis
    proof (cases "ins k x t")
      case (T_i x1)
      then show ?thesis unfolding ins.simps using T_i Node split_res
          suborders split_app Nil \<open>order_i k (ins k x t)\<close>
        using order.simps(2) by auto
    next
      case (Up_i x21 x22 x23)
      then show ?thesis unfolding ins.simps
        using Up_i Nil Node split_res \<open>order_i k (ins k x t)\<close> suborders split_app Nil node_i_order_i[of k "l@[(x21,x22)]" x23]
        by (auto simp del: node_i.simps)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using Node a_prod Cons split_res by simp
    next
      case False
      then have "order_i k (ins k x sub)"
        using Node suborders split_res a_prod local.Cons split_fun.split_fun_set(1) split_fun_axioms by fastforce
      show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then show ?thesis unfolding ins.simps
          using suborders split_app Cons \<open>order_i k (local.ins k x sub)\<close> T_i Cons Node split_res a_prod
          by auto
      next
        case (Up_i x21 x22 x23)
          (* The only case where explicit reasoning is required - likely due to the insertion of 2 elements in the list *)
        then have "order k t"
          using Node by auto
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
        then show ?thesis  unfolding ins.simps using Up_i Cons Node split_res a_prod
          by simp
      qed
    qed
  qed
qed simp

thm bal.simps

fun bal_i where
"bal_i (T_i t) = bal t" |
"bal_i (Up_i l a r) = (height l = height r \<and> bal l \<and> bal r)"

lemma in_subtrees_drop: "set (subtrees (drop n xs)) \<subseteq> set (subtrees xs)"
  apply(induction xs)
   apply(simp_all) 
  using image_iff in_set_dropD by fastforce

lemma in_subtrees_take: "set (subtrees (take n xs)) \<subseteq> set (subtrees xs)"
  apply(induction xs)
   apply(simp_all) 
  using image_iff in_set_takeD by fastforce

fun height_i where
"height_i (T_i t) = height t" |
"height_i (Up_i l a r) = max (height l) (height r)"

lemma node_i_bal_i:
  assumes "\<forall>x \<in> set (subtrees ts). bal x"
    and "bal t"
  and "\<forall>x \<in> set (subtrees ts). height t = height x"
shows "bal_i (node_i k ts t)"
  apply(cases "length ts \<le> 2*k")
   apply(auto split: list.splits simp add: assms height_bal_tree fold_max_set in_subtrees_drop in_subtrees_take)
  oops

lemma node_i_bal_i:
  assumes "\<forall>x \<in> set (subtrees ts). bal x"
    and "bal t"
  and "\<forall>x \<in> set (subtrees ts). height t = height x"
shows "bal_i (node_i k ts t)"
proof(cases "length ts \<le> 2* k")
  case False
  then have "length ts > 0" by linarith
  then obtain sub sep rs where list_drop: "drop (length ts div 2) ts = (sub,sep)#rs"
    by (metis Cons_nth_drop_Suc drop0 eq_snd_iff neq_Nil_conv split_fun.drop_not_empty split_fun_axioms)
  then have "\<forall>s \<in> set (subtrees ((sub,sep)#rs)). height s = height t"
    using in_subtrees_drop assms by (metis subsetD)
  then have 1: "bal (Node rs t)"
    unfolding bal.simps using assms list_drop
    by (metis Cons_nth_drop_Suc drop_eq_Nil in_subtrees_drop le_less_linear list.discI list.inject subset_code(1))


  have "height t = height sub"
    by (simp add: \<open>\<forall>s\<in>set (subtrees ((sub, sep) # rs)). height s = height t\<close>)
  then have 2: "bal (Node (take (length ts div 2) ts) sub)"
    unfolding bal.simps using assms
    by (metis in_subtrees_drop in_subtrees_take list.set_intros(1) list_drop some_child_sub(1) subsetD)

  have "height (Node (take (length ts div 2) ts) sub) = Suc (height t)"
    using "2" \<open>BTree.height_class.height t = BTree.height_class.height sub\<close> height_bal_tree by auto
  moreover have "height (Node rs t) = Suc (height t)"
    using "1" height_bal_tree by blast
  ultimately have "bal_i (Up_i (Node (take (length ts div 2) ts) sub) sep (Node rs t))"
    using 1 2 by simp
  then show ?thesis unfolding node_i.simps using 1 2 False list_drop by simp
qed (simp add: assms)

find_theorems fold max
thm Max.union


lemma fold_max_max: "max (a::(_::linorder)) (fold max bs b) = fold max bs (max a b)"
  apply(induction bs arbitrary: a b)
  apply(auto simp add: max.left_commute)
  done

lemma max_sep_fold_max: "max (fold max as (a::(_::linorder))) (fold max bs b) = (fold max (as@a#bs) b)"
  apply(induction as arbitrary: a bs b)
   apply(auto simp add: max.assoc max.left_commute fold_max_max)
  done

lemma height_list_drop_eq: "\<lbrakk>ls@(a,b)#rs = ts\<rbrakk> \<Longrightarrow> height_i (Up_i (Node ls a) b (Node rs t)) = height (Node ts t) "
  by (auto simp add: fold_max_max max.commute)

lemma node_i_height_i: "height_i (node_i k ts t) = height (Node ts t)"
  apply(auto split: list.splits simp del: height_btree.simps)
  by (metis append_take_drop_id height_i.simps(2) height_list_drop_eq)

lemma ins_height_i: "height_i (ins k x t) = height t"
  apply(induction k x t rule: ins.induct)
   apply(auto split!: prod.split list.split up_i.split simp del: node_i.simps
 simp add: split_fun_req node_i_height_i fold_max_max max_sep_fold_max)
  using split_fun_req(1) apply fastforce
    apply (metis append_Nil2 split_fun_req(1))
proof -
fix ka :: nat and xa :: 'a and ts :: "('a btree \<times> 'a) list" and ta :: "'a btree" and x1 :: "('a btree \<times> 'a) list" and a :: "'a btree" and b :: 'a and x22 :: "('a btree \<times> 'a) list" and x1a :: "'a btree"
  assume a1: "split_fun ts xa = (x1, (a, b) # x22)"
have f2: "\<forall>n ns na. max (n::nat) (fold max ns na) = fold max ns (max n na)"
  using fold_max_max by blast
  have "x1 @ (a, b) # x22 = ts"
    using a1 by (simp add: split_fun_req(1))
  then show "fold max (map (BTree.height_class.height \<circ> fst) x22) (fold max (map (BTree.height_class.height \<circ> fst) x1) (max (BTree.height_class.height a) (BTree.height_class.height ta))) = fold max (map (BTree.height_class.height \<circ> fst) ts) (BTree.height_class.height ta)"
    using f2 by force
next
  show "\<And>k x ts t x1 a b x22 x21 x22a x23.
       (\<And>y. False \<Longrightarrow> y = [] \<Longrightarrow> height_i (local.ins k x t) = BTree.height_class.height t) \<Longrightarrow>
       (\<And>xa y aa ba x22a xb ya.
           xa = x1 \<and> aa = a \<and> ba = b \<and> x22a = x22 \<Longrightarrow>
           y = (a, b) # x22 \<Longrightarrow>
           xb = a \<and> ya = b \<Longrightarrow>
           max (BTree.height_class.height x21) (BTree.height_class.height x23) =
           BTree.height_class.height a) \<Longrightarrow>
       split_fun ts x = (x1, (a, b) # x22) \<Longrightarrow>
       local.ins k x a = Up_i x21 x22a x23 \<Longrightarrow>
       fold max (map (BTree.height_class.height \<circ> fst) x22)
        (fold max (map (BTree.height_class.height \<circ> fst) x1)
          (max (BTree.height_class.height x23)
            (max (BTree.height_class.height x21) (BTree.height_class.height t)))) =
       fold max (map (BTree.height_class.height \<circ> fst) ts) (BTree.height_class.height t)"
(* TODO this employs a heuristic solver *)
    by (smt comp_eq_dest_lhs fold_max_max fst_conv list.simps(9) map_append max.commute max_sep_fold_max split_fun_req(1)) 
qed


lemma "bal t \<Longrightarrow> bal_i (ins k x t)"
  apply(induction k x t rule: ins.induct)
   apply(auto simp del: node_i.simps split!: prod.splits list.splits up_i.splits
 simp add: node_i_bal_i split_fun_def split_fun_axioms split_fun_req ins_height_i)
  
  apply (metis append_self_conv fst_conv height_i.simps(1) ins_height_i split_fun_req(1))
  using split_fun_req(1) apply fastforce
  oops

(* the below proof is overly complicated as a number of lemmas regarding height are missing *)
lemma "bal t \<Longrightarrow> bal_i (ins k x t)"
proof(induction t)
  case (Node ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce
  
  show ?case
  proof (cases r)
    case Nil
    then show ?thesis 
    proof (cases "ins k x t")
      case (T_i x1)
      then have "bal (Node l x1)" unfolding bal.simps
        by (metis Node BTree.bal.simps(2) append_Nil2 bal_i.simps(1) height_i.simps(1) ins_height_i local.Nil split_app)
      then show ?thesis unfolding ins.simps using Nil T_i Node split_res by simp
    next
      case (Up_i x21 x22 x23)
      then have 
        "(\<forall>x\<in>set (subtrees (l@[(x21,x22)])). BTree.bal x)"
        "BTree.bal x23"
        "(\<forall>x\<in>set (subtrees l). BTree.height_class.height x23 = BTree.height_class.height x)"
        using Node Up_i local.Nil split_res split_app
        by simp_all (metis height_i.simps(2) ins_height_i max_def)
      then show ?thesis unfolding ins.simps
        using Up_i Nil Node split_res by(simp del: node_i.simps add: node_i_bal_i)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using a_prod Node split_res Cons by simp
    next
      case False
      then have "bal_i (ins k x sub)" using Node split_res
        by (metis BTree.bal.simps(2) a_prod local.Cons prod_set_simps(1) singletonI some_child_sub(1) split_fun.split_fun_child split_fun_axioms)
      show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then have "bal x1" "height x1 = height t"
          using Node T_i \<open>bal_i (local.ins k x sub)\<close>
          by simp (metis Node.prems BTree.bal.simps(2) T_i a_prod height_i.simps(1) ins_height_i local.Cons some_child_sub(1) split_fun_child split_res)
        then show ?thesis
          using split_app Cons T_i Node split_res a_prod
          by auto
      next
        case (Up_i x21 x22 x23)
          (* The only case where explicit reasoning is required - likely due to the insertion of 2 elements in the list *)
        then have "bal t"
          using Node by auto
        moreover have
          "\<forall>x \<in> set (subtrees (l@(x21,x22)#(x23,sep)#list)). bal x"
          using Up_i split_app Cons Node \<open>bal_i (ins k x sub)\<close> by auto
        moreover have "\<forall>x \<in> set (subtrees (l@(x21,x22)#(x23,sep)#list)). height x = height t"
          using False Up_i split_app Cons Node \<open>bal_i (ins k x sub)\<close> ins_height_i split_res a_prod
          apply auto
          apply (metis height_i.simps(2) max_def)
           apply (metis Un_iff fst_conv)+
          done
        ultimately have "bal_i (node_i k (l@(x21,x22)#(x23,sep)#list) t)"
          using node_i_bal_i[of "(l@(x21,x22)#(x23,sep)#list)" t] by (simp del: node_i.simps)
        then show ?thesis unfolding ins.simps using Up_i Cons Node split_res a_prod
          by simp
      qed
    qed
  qed
qed simp

(* ins acts as a Set insertion *)

fun set_up_i where
"set_up_i (T_i t) = set_btree t" |
"set_up_i (Up_i l a r) = set_btree l \<union> set_btree r \<union> {a}"

thm BTree.set_btree_induct

lemma set_drop_take: "set l = set (drop n l) \<union> set (take n l)"
  by (metis append_take_drop_id set_append sup_commute)

lemma node_i_set: "set_up_i (node_i k ts t) = set_btree (Node ts t)"
proof (cases "length ts \<le> 2*k")
  case False
  then have "length ts > 0" by linarith
  then obtain sub sep rs where drop_split: "drop (length ts div 2) ts = (sub,sep)#rs"
    by (metis Cons_nth_drop_Suc drop0 drop_not_empty eq_snd_iff neq_Nil_conv)
  then have "set_btree (Node ts t) = (\<Union>x \<in> set ts. \<Union> (set_btree ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x) \<union> set_btree t"
    by simp
  also have "\<dots> = (\<Union>x \<in> set (drop (length ts div 2) ts) \<union> set (take (length ts div 2) ts). \<Union> (set_btree ` Basic_BNFs.fsts x) \<union> Basic_BNFs.snds x) \<union> set_btree t"
    using set_drop_take[of ts "length ts div 2"] by simp
  also have "\<dots> = set_up_i (Up_i (Node (take (length ts div 2) ts) sub) sep (Node rs t))" using drop_split by auto
  also have "\<dots> = set_up_i (node_i k ts t)" using False drop_split by simp
  finally show ?thesis  by simp
qed simp

find_theorems set_btree
thm btree.set

lemma set_btree_split: "set_btree (Node (l@(sub,sep)#r) t) = set_btree (Node (l@r) t) \<union> set_btree sub \<union> {sep}"
  apply(induction r)
   apply(auto)
  done

lemma ins_set: "set_up_i (ins k x t) = set_btree t \<union> {x}"
proof(induction t)
  case (Node ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce
  
  show ?case
  proof (cases r)
    case Nil

    show ?thesis 
    proof (cases "ins k x t")
      case (T_i x1)
      then have "set_btree (Node l x1) = set_btree (Node ts t) \<union> {x}"
        using Node split_app Nil by auto
      then show ?thesis
        by (simp add: T_i local.Nil split_res)
    next
      case (Up_i x21 x22 x23)
      then have t0: "set_up_i (Up_i x21 x22 x23) = set_btree t \<union> {x}" using Node by auto
      then have "set_up_i (node_i k (l@[(x21,x22)]) x23) = set_btree (Node (l@[(x21,x22)]) x23)"
        using node_i_set by (simp del: node_i.simps)
      also have "\<dots> = set_btree (Node ts t) \<union> {x}" using Node split_app Nil t0 by auto
      finally show ?thesis
        by (simp add: Up_i local.Nil split_res)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then show ?thesis
    proof (cases "sep = x")
      case False
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then have "set_btree x1 = set_btree sub \<union> {x}"
          using Node a_split split_app Cons by fastforce
        then have "set_btree (Node (l @ (x1,sep) # list) t) = set_btree (Node (l @ (sub,sep) # list) t) \<union> {x}"
          using set_btree_split by auto
        also have "\<dots> = set_btree (Node ts t) \<union> {x}" using split_app Cons a_split by simp
        finally show ?thesis
          using Node Cons a_split split_res T_i False by simp
      next
        case (Up_i x21 x22 x23)
        then have t0: "set_btree x21 \<union> {x22} \<union> set_btree x23 = set_btree sub \<union> {x}"
          using Node a_split split_app Cons by fastforce
        then have "set_up_i (node_i k (l @ (x21,x22)#(x23,sep)#list) t) = set_btree (Node (l @ (x21,x22)#(x23,sep)#list) t)"
          using node_i_set by (simp del: node_i.simps)
        also have "\<dots> = set_btree (Node (l@(sub,sep)#list) t) \<union> {x}"
          using t0 set_btree_split by auto
        also have "\<dots> = set_btree (Node ts t) \<union> {x}"
          using split_app Cons a_split by simp
        finally show ?thesis unfolding ins.simps 
          using Up_i a_split local.Cons split_app split_res False by simp
      qed
    next
      case True
      then have "x \<in> set_btree (Node ts t)"
        by (metis a_split btree.set_intros(2) local.Cons prod_set_simps(2) singletonI split_fun_child split_res)
      then have "set_btree (Node ts t) = set_btree (Node ts t) \<union> {x}" by blast
      then show ?thesis using a_split Node Cons True split_res by simp
    qed
  qed
qed simp


(* TODO sorted invariant *)

thm sorted_alt.simps

find_theorems sorted_wrt take

fun sorted_up_i where
"sorted_up_i (T_i t) = sorted_alt t" |
"sorted_up_i (Up_i l a r) = (sorted_alt l \<and> sorted_alt r \<and> sub_sep_cons (l,a) \<and> (\<forall>y \<in> set_btree r. a < y))"


lemma sorted_alt_split_rs: "sorted_alt (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_alt (Node rs t)"
  apply(induction ls)
   apply(auto)
  done

lemma sorted_alt_split_ls: "sorted_alt (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_alt (Node ls sub)"
  apply(induction ls)
   apply(auto)
  done


lemma node_i_sorted:
  assumes "sorted_alt (Node ts t)"
  shows "sorted_up_i (node_i k ts t)"
using assms proof(cases "length ts \<le> 2*k")
  case False
  then have "length ts > 0" by linarith
  then obtain sub sep rs where list_drop: "drop (length ts div 2) ts = (sub,sep)#rs"
    by (metis Cons_nth_drop_Suc drop0 eq_snd_iff neq_Nil_conv split_fun.drop_not_empty split_fun_axioms)
  then have sorted_list_drop: "sorted_wrt sub_sep_sm ((sub,sep)#rs)"
    by (metis sorted_wrt_drop assms sorted_alt.simps(2))

  let ?take = "take (length ts div 2) ts"
  have "sorted_up_i (Up_i (Node ?take sub) sep (Node rs t))"
    unfolding sorted_up_i.simps
  proof (safe)
    from sorted_list_drop have
      "\<forall>r \<in> set (subtrees rs). \<forall>x \<in> set_btree r. sep < x"
      "\<forall>r \<in> set (seperators rs). sep < r"
      by (auto simp add: sorted_wrt_sorted_left)
    then show "\<And>x. x \<in> set_btree (Node rs t) \<Longrightarrow> sep < x"
      by (metis assms list.set_intros(1) list_drop set_btree_induct set_drop_subset some_child_sub(2) sorted_alt.simps(2) subset_code(1))
  next
    show "sorted_alt (Node rs t)"
      using list_drop sorted_alt_split_rs assms append_take_drop_id
      by metis
  next
    show "sorted_alt (Node ?take sub)"
      using list_drop sorted_alt_split_ls assms append_take_drop_id
      by metis
  next
    show "sub_sep_cons (Node ?take sub, sep)"
      by (metis (no_types, lifting) append_take_drop_id assms list_drop sorted_alt.simps(2) sorted_wrt_sorted_right2 sub_sep_cons.simps)
  qed
  then show ?thesis
    using False list_drop by simp
qed simp

thm btree.set
thm sorted_wrt_append



(* TODO sorted of ins *)
lemma "sorted_alt t \<Longrightarrow> sorted_up_i (ins k x t)"
proof (induction t)
  case (Node ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls,rs)" by (cases "split_fun ts x")
  then show ?case
  proof (cases "rs")
    case Nil
    then have ls_sorted: "sorted_alt (Node ls t)" 
        using list_split Node.prems split_fun_req(1) by fastforce
    show ?thesis
    proof (cases "ins k x t")
      case (T_i x1) (* braucht evtl eine schönere formulierung für die sortierung/mengen von baum*sep listen *)
      then have "sorted_alt x1" using Node by simp
      moreover have "\<forall>y \<in> set_btree x1. \<forall> sep \<in> set (seperators ls). sep < y"
      proof
        fix y assume "y \<in> set_btree x1"
        then have "y \<in> set_btree t \<or> y = x"
          using T_i ins_set by (metis UnE set_up_i.simps(1) singletonD)
        then show "\<forall>sep \<in> set (seperators ls). sep < y"
          by (meson ls_sorted Node.prems calculation(1) list_split sorted_alt.simps(2) sorted_wrt_list_sorted split_fun_req(2))
      qed
      ultimately show ?thesis
        using ls_sorted
        by (simp add: T_i list_split local.Nil)
    next
      case (Up_i l a r)
      
      have "\<forall>b \<in> set ls. sub_sep_sm b (l, a)"
      proof
        fix b assume "b \<in> set ls"
        obtain sub_l sep_l where "b = (sub_l, sep_l)" by (cases b)
        then have "sep_l < x"
          using Node.prems \<open>b \<in> set ls\<close> list_split sorted_wrt_list_sorted split_fun_req(2) by fastforce
        moreover have "\<forall>y \<in> set_btree t. sep_l < y"
          using Node.prems \<open>b = (sub_l, sep_l)\<close> \<open>b \<in> set ls\<close> list_split local.Nil split_fun_set_l by auto
        moreover have "set_btree l \<union> {a} \<subseteq> set_btree t \<union> {x}"
          by (metis Up_i ins_set insert_absorb2 set_up_i.simps(2) singleton_insert_inj_eq sup.mono sup_ge1)
        ultimately show "sub_sep_sm b (l,a)"
          using \<open>b = (sub_l, sep_l)\<close> by auto
      qed
      then have "sorted_wrt sub_sep_sm (ls@[(l,a)])"
        using sorted_wrt_append ls_sorted by fastforce
      moreover have "sorted_alt r" using Up_i Node by auto
      moreover have "\<forall>y \<in> set_btree r. y < a" using Up_i Node sorry
      moreover have "\<forall>y \<in> set_btree r. \<forall>x \<in> set (seperators ls). x < y" sorry
      ultimately have "sorted_alt (Node (ls@[(l,a)]) r)" sorry
      then show ?thesis sorry
    qed
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed simp

end



(*TODO: at some point this better be replaced with something binary search like *)
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
  by (metis Pair_inject)

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
  using assms linear_split_sm linear_split_gr by fastforce+

interpretation btree_linear_search: split_fun "linear_split"
  by (simp add: linear_split_req linear_split_append split_fun_def)



end