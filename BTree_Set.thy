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

lemma split_fun_child: " split_fun xs y = (ls, a # rs) \<Longrightarrow>
       a \<in> set xs"
  using split_fun_req(1) by fastforce

lemma [termination_simp]:"(x, (a, b) # x22) = split_fun t y \<Longrightarrow>
      size a < Suc (size_list (\<lambda>x. Suc (size (fst x))) t  + size l)"
  by (metis group_cancel.add1 plus_1_eq_Suc some_child_sub(1) split_fun_child subtree_smaller trans_less_add1)

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
      using choose_split split_fun_subtree_match "2.prems"(1) asms choose_split split_fun_subtree_match(2)
      by auto
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


fun node_i:: "nat \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> 'a btree \<Rightarrow> 'a up_i" where
"node_i k xs x = (
if length xs \<le> 2*k then T_i (Node xs x)
else (
  case drop (length xs div 2) xs of (sub,sep)#rs \<Rightarrow>
    Up_i (Node (take (length xs div 2) xs) sub) sep (Node rs x)
  )
)"


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


fun tree_i where
"tree_i (T_i sub) = sub" |
"tree_i (Up_i l a r) = (Node [(l,a)] r)"

fun insert where
  "insert k x t = tree_i (ins k x t)"

(* proofs *)

fun order_up_i where
"order_up_i k (T_i sub) = order k sub" |
"order_up_i k (Up_i l a r) = (order k l \<and> order k r)"

fun root_order_up_i where
"root_order_up_i k (T_i sub) = root_order k sub" |
"root_order_up_i k (Up_i l a r) = (order k l \<and> order k r)"


fun inorder_up_i where
"inorder_up_i (T_i sub) = inorder sub" |
"inorder_up_i (Up_i l a r) = (inorder l @ [a]) @ inorder r"

lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto)
  done

lemma node_i_root_order:
  assumes "length ts > 0"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "root_order_up_i k (node_i k ts t)"
proof (cases "length ts \<le> 2*k")
case True
  then show ?thesis using set_map_pred_eq assms by simp
next
  case False
  then have length_ts: "length ts > 0"
    by linarith
  then have "drop (length ts div 2) ts \<noteq> []"
    using drop_not_empty by auto
  then obtain sub sep rs where drop_ts: "drop (length ts div 2) ts = (sub,sep)#rs" 
    by (metis eq_snd_iff hd_Cons_tl)
  then have length_rs: "length rs = length ts - (length ts div 2) - 1" using length_drop
    by (metis One_nat_def add_diff_cancel_right' list.size(4))
  also have "\<dots> \<le> 4*k - ((4*k + 1) div 2)" using assms(2) by simp
  also have "\<dots> = 2*k" by auto
  finally have "length rs \<le> 2*k" by simp
  moreover have "length rs \<ge> k" using False length_rs by simp
  moreover have "set ((sub,sep)#rs) \<subseteq> set ts"
    by (metis drop_ts set_drop_subset)
  ultimately have o_r: "order k sub" "order k (Node rs t)" using drop_ts assms drop_ts by auto
  moreover have "length (take (length ts div 2) ts) \<ge> k"
    using length_take assms length_ts False by simp
  moreover have  "length (take (length ts div 2) ts) \<le> 2*k"
    using assms(2) by auto
  ultimately have o_l: "order k (Node (take (length ts div 2) ts) sub)"
    using set_take_subset assms by fastforce
  from o_r o_l have "order_up_i k (Up_i (Node (take (length ts div 2) ts) sub) sep (Node rs t))" by simp
  then show ?thesis unfolding node_i.simps
    by (simp add: False drop_ts)
qed

lemma node_i_order_helper:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "case (node_i k ts t) of T_i t \<Rightarrow> order k t | _ \<Rightarrow> True"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis using set_map_pred_eq assms by simp
next
  case False
  then have length_ts: "length ts > 0"
    by linarith
  then have "drop (length ts div 2) ts \<noteq> []"
    using drop_not_empty by auto
  then obtain sub sep rs where drop_ts: "drop (length ts div 2) ts = (sub,sep)#rs" 
    by (metis eq_snd_iff hd_Cons_tl)
  then show ?thesis
    unfolding node_i.simps
    using assms by auto
qed

lemma node_i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "order_up_i k (node_i k ts t)"
  using node_i_root_order node_i_order_helper assms
  apply(cases "node_i k ts t")
   apply fastforce
  apply (metis assms(1) assms(2) assms(3) assms(4) le_0_eq le_less_linear mult_0_right node_i.simps node_i_root_order order_up_i.simps(2) root_order_up_i.simps(2) up_i.distinct(1))
  done


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

thm fst_conv

lemma xs_split_fun_prop: 
  "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> P a"
 (* "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> \<forall>x \<in> set ls. P (fst x)"
  "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> \<forall>x \<in> set rs. P (fst x)"*)
  using split_fun_req(1) by fastforce+


lemma length_lemma:
"split_fun ts x = (ls, (a,b)#rs) \<Longrightarrow> length (ls@(a,b)#rs) = length (ls@(c,d)#(e,f)#rs) - 1"
"split_fun ts x = (ls, (a,b)#rs) \<Longrightarrow> length (ls@rs) = length (ls@(a,b)#rs) - 1"
  by auto

lemma help_lem:
  assumes  "\<forall>x \<in> set ls. P (fst x)" "\<forall>x \<in> set rs. P (fst x)"
    and "P a" "P c"
  shows "\<forall>x \<in> set (ls@(a,b)#(c,d)#rs). P (fst x)"
  using assms by(auto)

thm node_i_order[of "_" "_@(_,_)#(_,_)#_" "_"]

(* "Automatic proof", using a number of lemmata 
lemma ins_order_alt: "order k t \<Longrightarrow> order_up_i k (ins k x t)"
  apply(induction k x t rule: ins.induct)
   apply(auto simp del: node_i.simps split!: prod.splits list.splits up_i.splits
 simp add: split_fun_length_l split_fun_length split_fun_set_l split_fun_set node_i_order xs_split_fun_prop
split_fun_req(1) length_lemma node_i_order[of "_" "_@(_,_)#(_,_)#_" "_"])
  subgoal for k x ts t x1 a b x22 x21 x22a x2
  proof -
    assume assms:
    "(\<And>y. False \<Longrightarrow> y = [] \<Longrightarrow> order_up_i k (local.ins k x t))"
    "(\<And>xa y aa ba x22a xb ya.
        xa = x1 \<and> aa = a \<and> ba = b \<and> x22a = x22 \<Longrightarrow>
        y = (a, b) # x22 \<Longrightarrow> xb = a \<and> ya = b \<Longrightarrow> order k x21 \<and> order k x2)"
    "k \<le> length ts"
    "length ts \<le> 2 * k"
    "\<forall>x\<in>set ts. order k (fst x)"
    "order k t"
    "split_fun ts x = (x1, (a, b) # x22)"
    "local.ins k x a = Up_i x21 x22a x2"
    "b \<noteq> x"
    then have "k \<le> length (x1 @ (x21, x22a) # (x2, b) # x22)" using split_fun_req(1) length_lemma by auto
    moreover have "length (x1@(x21,x22a)#(x2,b)#x22) \<le> 4*k+1" using split_fun_req(1) length_lemma assms by auto
    moreover have "\<forall>x \<in> set (x1@(x21,x22a)#(x2,b)#x22). order k (fst x)" using assms
      using split_fun_set by auto
    moreover have "order k t" using assms by auto
    ultimately show "order_up_i k (node_i k (x1 @ (x21, x22a) # (x2, b) # x22) t)" using node_i_order[of k "_@(_,_)#(_,_)#_" t] by (auto simp del: node_i.simps)
  qed
  done *)

(* direct proof *)
lemma ins_order: 
   "order k t \<Longrightarrow> order_up_i k (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce

  show ?case
  proof (cases r)
    case Nil
    then have "order_up_i k (ins k x t)" using 2 split_res
      by simp
    then show ?thesis
      using Nil 2 split_app split_res  split_app Nil node_i_order
        by (auto split!: up_i.splits simp del: node_i.simps)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using 2 a_prod Cons split_res by simp
    next
      case False
      then have "order_up_i k (ins k x sub)"
        using 2 split_res a_prod local.Cons split_fun.split_fun_set(1) split_fun_axioms
        by fastforce
      show ?thesis
          using 2 split_app Cons length_append node_i_order a_prod split_res
            \<open>order_up_i k (local.ins k x sub)\<close>
          by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp


(* notice this is almost a duplicate of ins_root_order *)
lemma ins_root_order: 
  assumes "root_order k t"
  shows "root_order_up_i k (ins k x t)"
proof(cases t)
  case (Node ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts" using split_fun_axioms split_fun_def
    by fastforce

  show ?thesis
  proof (cases r)
    case Nil
    then have "order_up_i k (ins k x t)" using Node assms split_res
      by (simp add: ins_order)
    then show ?thesis
      using Nil Node split_app split_res assms  split_app Nil node_i_root_order
        by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using assms Node a_prod Cons split_res by simp
    next
      case False
      then have "order_up_i k (ins k x sub)"
        using Node assms split_res a_prod local.Cons split_fun.split_fun_set(1) split_fun_axioms
        by (metis ins_order root_order.simps(2) some_child_sub(1))
      show ?thesis
          using assms split_app Cons length_append Node node_i_root_order a_prod split_res
            \<open>order_up_i k (local.ins k x sub)\<close>  node_i_root_order[of "(l@(_,_)#(_,sep)#list)" k t]
          by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp

thm bal.simps

fun bal_up_i where
"bal_up_i (T_i t) = bal t" |
"bal_up_i (Up_i l a r) = (height l = height r \<and> bal l \<and> bal r)"

lemma in_subtrees_drop: "set (subtrees (drop n xs)) \<subseteq> set (subtrees xs)"
  apply(induction xs)
   apply(simp_all) 
  using image_iff in_set_dropD by fastforce

lemma in_subtrees_take: "set (subtrees (take n xs)) \<subseteq> set (subtrees xs)"
  apply(induction xs)
   apply(simp_all) 
  using image_iff in_set_takeD by fastforce

fun height_up_i where
"height_up_i (T_i t) = height t" |
"height_up_i (Up_i l a r) = max (height l) (height r)"

lemma node_i_bal:
  assumes "\<forall>x \<in> set (subtrees ts). bal x"
    and "bal t"
  and "\<forall>x \<in> set (subtrees ts). height t = height x"
shows "bal_up_i (node_i k ts t)"
  apply(cases "length ts \<le> 2*k")
   apply(auto split: list.splits simp add: assms height_bal_tree fold_max_set in_subtrees_drop in_subtrees_take)
  oops

lemma node_i_bal:
  assumes "\<forall>x \<in> set (subtrees ts). bal x"
    and "bal t"
  and "\<forall>x \<in> set (subtrees ts). height t = height x"
shows "bal_up_i (node_i k ts t)"
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
  ultimately have "bal_up_i (Up_i (Node (take (length ts div 2) ts) sub) sep (Node rs t))"
    using 1 2 by simp
  then show ?thesis unfolding node_i.simps using 1 2 False list_drop by simp
qed (simp add: assms)

find_theorems fold max
thm Max.union


lemma height_list_drop_eq: "\<lbrakk>ls@(a,b)#rs = ts\<rbrakk> \<Longrightarrow> height_up_i (Up_i (Node ls a) b (Node rs t)) = height (Node ts t) "
  by (auto simp add: fold_max_max max.commute)

lemma node_i_height: "height_up_i (node_i k ts t) = height (Node ts t)"
  apply(auto split: list.splits simp del: height_btree.simps)
  by (metis append_take_drop_id height_up_i.simps(2) height_list_drop_eq)


lemma ins_height: "height_up_i (ins k x t) = height t"
proof(induction t)
  case (Node ts t)
  then obtain ls rs where split_list: "split_fun ts x = (ls,rs)"
    by (meson surj_pair)
  then have split_list_append: "ls@rs = ts"
    using split_fun_req(1) by auto
  then show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
    proof (cases "ins k x t")
      case (T_i x1)
      then have "height (Node ts t) = height (Node ls x1)"
        using Nil split_list_append Node.IH by auto
      then show ?thesis
        by (simp add: T_i Nil local.split_list)
    next
      case (Up_i x21 x22 x23)
      then have "height (Node ts t) = Suc (fold max (map height (subtrees ls)) (max (height x21) (height x23)))"
        using Nil split_list_append Node by auto
      also have "\<dots> = height (Node (ls@[(x21,x22)]) x23)" using fold_max_append by auto
      finally show ?thesis using Node Nil split_list Up_i
        by (simp del: node_i.simps add: node_i_height)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using Cons a_split Node split_list by (simp del: height_btree.simps)
    next
      case False
      then have height_sub: "height_up_i (ins k x sub) = height sub"
        by (metis Node.IH(1) a_split fst_conv fsts.intros local.Cons local.split_list split_fun_child)
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then have "height x1 = height sub" using height_sub by auto
        then have "fold max (map height (subtrees ts)) = fold max (map height (subtrees (ls@(x1,sep)#list)))"
          using Cons a_split split_list_append subtrees_split set_eq_fold by auto
        then show ?thesis 
          using T_i height_sub False Cons Node split_list a_split by auto
      next
        case (Up_i x21 x22 x23)
        then have "max (height x21) (height x23) = height sub" using height_sub by auto
        then have "height (Node ts t) = max (Suc (max (height x21) (height x23))) (height (Node (ls@list) t))"
          using Cons a_split split_list_append fold_max_extract
          by auto
        also have "\<dots> = Suc (max (height x21) (fold max (map height ((subtrees ls)@x23#(subtrees list))) (height t)))"
          by (simp add: fold_max_max)
        also have "\<dots> = Suc (fold max (map height ((subtrees ls)@x21#x23#(subtrees list))) (height t))"
          by (metis (no_types, lifting) fold_max_extract list.simps(9) map_append)
        also have "\<dots> = height (Node (ls@(x21,x22)#(x23,sep)#list) t)" by auto
        finally show ?thesis
          using Up_i height_sub False Cons Node split_list a_split by (auto simp del: node_i.simps simp add: node_i_height)
      qed
    qed
  qed
qed simp


(* the below proof is overly complicated as a number of lemmas regarding height are missing *)
lemma ins_bal: "bal t \<Longrightarrow> bal_up_i (ins k x t)"
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
        by (metis BTree.bal.simps(2) Node.IH(2) Node.prems append_Nil2 bal_up_i.simps(1) height_up_i.simps(1) ins_height local.Nil split_app)
      then show ?thesis unfolding ins.simps using Nil T_i Node split_res by simp
    next
      case (Up_i x21 x22 x23)
      then have 
        "(\<forall>x\<in>set (subtrees (l@[(x21,x22)])). BTree.bal x)"
        "BTree.bal x23"
        "(\<forall>x\<in>set (subtrees l). BTree.height_class.height x23 = BTree.height_class.height x)"
        using Node Up_i local.Nil split_res split_app
        by simp_all (metis height_up_i.simps(2) ins_height max_def)
      then show ?thesis unfolding ins.simps
        using Up_i Nil Node split_res by(simp del: node_i.simps add: node_i_bal)
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
      then have "bal_up_i (ins k x sub)" using Node split_res
        by (metis BTree.bal.simps(2) a_prod local.Cons prod_set_simps(1) singletonI some_child_sub(1) split_fun.split_fun_child split_fun_axioms)
      show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then have "bal x1" "height x1 = height t"
          using Node T_i \<open>bal_up_i (local.ins k x sub)\<close>
          by simp (metis Node.prems BTree.bal.simps(2) T_i a_prod height_up_i.simps(1) ins_height local.Cons some_child_sub(1) split_fun_child split_res)
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
          using Up_i split_app Cons Node \<open>bal_up_i (ins k x sub)\<close> by auto
        moreover have "\<forall>x \<in> set (subtrees (l@(x21,x22)#(x23,sep)#list)). height x = height t"
          using False Up_i split_app Cons Node \<open>bal_up_i (ins k x sub)\<close> ins_height split_res a_prod
          by simp_all (metis Node.prems bal.simps(2) bal_split fst_conv height_up_i.simps(2) image_Un set_append set_map split_fun_child subtrees.simps sup.idem sup_nat_def)
        ultimately show ?thesis using Up_i Cons Node split_res a_prod
          by (simp del: node_i.simps add: node_i_bal)
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


lemma ins_set: "set_up_i (ins k x t) = set_btree t \<union> {x}"
proof(induction t)
  case (Node ts t)
  then obtain l r where split_res: "split_fun ts x = (l, r)"
    by (meson surj_pair)
  then have split_app: "l@r = ts"
    using split_fun_req(1) by auto
  
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
          using Node a_split split_app Cons
          by (metis prod_set_simps(1) set_up_i.simps(2) singletonI split_fun_child split_res sup_assoc sup_commute)
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


(* sorted invariant *)

thm sorted_alt.simps

find_theorems sorted_wrt take

fun sorted_up_i where
"sorted_up_i (T_i t) = sorted_alt t" |
"sorted_up_i (Up_i l a r) = (sorted_alt l \<and> sorted_alt r \<and> sub_sep_cons (l,a) \<and> (\<forall>y \<in> set_btree r. a < y))"


lemma sorted_alt_split_rs: "sorted_alt (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_alt (Node rs t) \<and>  (\<forall>r \<in> set (seperators rs). sep < r)"
  apply(induction ls)
   apply(auto)
  done

lemma sorted_alt_split_ls: "sorted_alt (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_alt (Node ls sub) \<and>  (\<forall>l \<in> set (seperators ls). l < sep)"
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

lemma sorted_wrt_split: "sorted_wrt sub_sep_sm (l@(a,(b::('a::linorder)))#r) =
   (sorted_wrt sub_sep_sm l \<and>
    sorted_wrt sub_sep_sm r \<and>
(\<forall>x \<in> set l. sub_sep_sm x (a,b)) \<and>
(\<forall>x \<in> set r. sub_sep_sm (a,b) x))"
  using sorted_wrt_append by fastforce


lemma sorted_r_indep: "sorted_wrt sub_sep_sm ((a,b)#rs) \<Longrightarrow> sorted_wrt sub_sep_sm ((x,b)#rs)"
  apply(cases rs)
   apply(auto)
  done


lemma sorted_r_forall: "sorted_wrt P (a#rs) \<Longrightarrow> \<forall>y \<in> set rs. P a y"
  by simp

lemma sorted_l_forall: "sorted_wrt P (ls@[a]) \<Longrightarrow> \<forall>y \<in> set ls. P y a"
  by (simp add: sorted_wrt_append)

lemma set_seperators_split: "set (seperators (l@(x,sep)#r)) = set (seperators l) \<union> set (seperators r) \<union> {sep}"
  apply(induction r)
   apply(auto)
  done

lemma set_subtrees_split: "set (subtrees (l@(sub,x)#r)) = set (subtrees l) \<union> set (subtrees r) \<union> {sub}"
  apply(induction r)
   apply(auto)
  done

lemma sub_sep_sm_trans: "\<lbrakk>sub_sep_sm (a::(('a::linorder) btree \<times> 'a)) b; sub_sep_sm b c\<rbrakk> \<Longrightarrow> sub_sep_sm a c"
proof -
  assume asms: "sub_sep_sm a b" "sub_sep_sm b c"
  obtain suba sepa where "a = (suba,sepa)" by (cases a)
  obtain subb sepb where "b = (subb,sepb)" by (cases b)
  obtain subc sepc where "c = (subc,sepc)" by (cases c)
  from asms have "sepa < sepb"
    by (simp add: \<open>a = (suba, sepa)\<close> \<open>b = (subb, sepb)\<close>)
  also have "\<dots> < sepc"
    using \<open>b = (subb, sepb)\<close> \<open>c = (subc, sepc)\<close> asms(2) by auto
  moreover have "\<forall>x \<in> set_btree subc. sepa < x"
    using \<open>b = (subb, sepb)\<close> \<open>c = (subc, sepc)\<close> asms(2) calculation(1) by auto
  ultimately show "sub_sep_sm a c" 
    using \<open>a = (suba, sepa)\<close> \<open>c = (subc, sepc)\<close> by auto
qed


lemma sorted_wrt_split2: "sorted_wrt sub_sep_sm (l@(a,(b::('a::linorder)))#(c,d)#r) =
   (sorted_wrt sub_sep_sm l \<and>
    sorted_wrt sub_sep_sm r \<and>
(\<forall>x \<in> set l. sub_sep_sm x (a,b)) \<and>
(\<forall>x \<in> set r. sub_sep_sm (c,d) x) \<and>
sub_sep_sm (a,b) (c,d))"
proof -
  have "sorted_wrt sub_sep_sm (l@(a,(b::('a::linorder)))#(c,d)#r) =
(sorted_wrt sub_sep_sm l \<and> sorted_wrt sub_sep_sm ((a,b)#(c,d)#r) \<and> (\<forall>x \<in> set l. \<forall>y \<in> set ((a,b)#(c,d)#r). sub_sep_sm x y))"
    using sorted_wrt_append by blast
  also have "\<dots> = (sorted_wrt sub_sep_sm l \<and> sorted_wrt sub_sep_sm r \<and> sorted_wrt sub_sep_sm ((a,b)#[(c,d)]) \<and> (\<forall>x \<in> set r. sub_sep_sm (a,b) x \<and> sub_sep_sm (c,d) x) \<and> (\<forall>x \<in> set l. \<forall>y \<in> set ((a,b)#(c,d)#r). sub_sep_sm x y))"
    using sorted_wrt_append by auto
  also have "\<dots> = (sorted_wrt sub_sep_sm l \<and> sorted_wrt sub_sep_sm r \<and> sub_sep_sm (a,b) (c,d) \<and> (\<forall>x \<in> set r. sub_sep_sm (a,b) x \<and> sub_sep_sm (c,d) x) \<and> (\<forall>x \<in> set l. sub_sep_sm x (a,b) \<and> sub_sep_sm x (c,d) \<and> (\<forall>y \<in> set r. sub_sep_sm x y)))"
    by auto
  also have "\<dots> = (
    sorted_wrt sub_sep_sm l \<and>
    sorted_wrt sub_sep_sm r \<and>
    (\<forall>x \<in> set l. sub_sep_sm x (a,b)) \<and>
    (\<forall>x \<in> set r. sub_sep_sm (c,d) x) \<and>
    sub_sep_sm (a,b) (c,d)
  )"
    using sub_sep_sm_trans by blast
  finally show ?thesis by simp
qed

(* sorted of ins *)
lemma ins_sorted: "sorted_alt t \<Longrightarrow> sorted_up_i (ins k x t)"
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
      moreover have "\<forall>x \<in> set (subtrees (ls@[(l,a)])). sorted_alt x"
        using Node.IH(2) Up_i ls_sorted by auto
      moreover have "\<forall>y \<in> set (ls@[(l,a)]). sub_sep_cons y"
        using Node.IH(2) Up_i ls_sorted by auto
      moreover have "\<forall>z \<in> set (seperators (ls@[(l,a)])). \<forall>y \<in> set_btree r. z < y"
      proof
        fix z assume "z \<in> set (seperators (ls@[(l,a)]))"
        then have "z \<in> set (seperators ls) \<or> z = a" by auto
        then show "\<forall>y \<in> set_btree r. z < y"
        proof
          assume "z \<in> set (seperators ls)"
          then have "z < x"
            using split_fun_req sorted_wrt_list_sorted Node.prems list_split by fastforce
          moreover have "\<forall>y \<in> set_btree t. z < y"
            using \<open>z \<in> set (seperators ls)\<close> ls_sorted sorted_alt.simps(2) by blast
          moreover have "set_btree r \<subseteq> set_btree t \<union> {x}"
            by (metis Up_i ins_set le_supI1 set_up_i.simps(2) sup_ge2)
          ultimately show "\<forall>y \<in> set_btree r. z < y"
            by blast
        next
          assume "z = a"
          then show "\<forall>y \<in> set_btree r. z < y" using Up_i Node by simp
        qed
      qed
      ultimately have "sorted_alt (Node (ls@[(l,a)]) r)" by simp
      then show ?thesis
        using Node Up_i list_split Nil  node_i_sorted[of "ls@[(l,a)]" r] by (simp del: node_i.simps)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    have sub_lists_sorted:
      "sorted_wrt sub_sep_sm (ls@(sub,sep)#[])"
      "sorted_wrt sub_sep_sm ((sub,sep)#list)"
      apply (metis (mono_tags, lifting) Node.prems a_split list_split local.Cons sorted_alt.simps(2) sorted_wrt_Cons sorted_wrt_split split_fun_req(1) sorted_wrt1)
      apply (metis (mono_tags, lifting) Node.prems list_split a_split local.Cons sorted_alt.simps(2) sorted_wrt_Cons sorted_wrt_split split_fun_req(1))
      done
    have sub_list_cons: "\<forall>x \<in> set (ls@(sub,sep)#list). sub_sep_cons x"
      using Node.prems a_split list_split local.Cons sorted_alt.simps(2) split_fun_req(1) by blast
    then show ?thesis
    proof (cases "sep = x")
      case True
      then show ?thesis using Node Cons True list_split a_split by simp
    next
      case False
      have sub_sorted: "sorted_up_i (ins k x sub)"
        using Node a_split list_split local.Cons split_fun.split_fun_set(1) split_fun_axioms by fastforce
      have sub_set: "set_up_i (ins k x sub) = set_btree sub \<union> {x}"
        by (simp add: ins_set)
      
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        have "sorted_alt (Node (ls@(x1,sep)#list) t)"
          unfolding sorted_alt.simps
        proof (safe)
          have "\<forall>y \<in> set ls. sub_sep_sm y (x1,sep)"
          proof
            fix y assume "y \<in> set ls"
            then obtain suby sepy where "y = (suby, sepy)"
              by (meson surj_pair)
            then have "sepy \<in> set (seperators ls)"
              using \<open>y \<in> set ls\<close> some_child_sub(2) by fastforce
            then have "sepy < x"
              by (meson Node.prems list_split sorted_alt.simps(2) sorted_wrt_list_sorted split_fun_req(2))
            moreover have "\<forall>z \<in> set_btree sub. sepy < z"
               using split_fun_req Cons list_split Node 
                 \<open>y = (suby, sepy)\<close> \<open>y \<in> set ls\<close> sorted_wrt_split sub_lists_sorted(1) by auto
            moreover have "sepy < sep"
               using split_fun_req Cons list_split Node
               by (metis (no_types, lifting) \<open>sepy \<in> set (seperators ls)\<close> a_split sorted_alt_split_ls)
            ultimately show "sub_sep_sm y (x1,sep)"
               using sub_sorted T_i \<open>y = (suby, sepy)\<close> sub_set by auto
           qed
         then show "sorted_wrt sub_sep_sm (ls@(x1,sep)#list)"
           using sorted_wrt_split sub_lists_sorted(1) sub_lists_sorted(2) by auto
        next
          fix a b
          assume "(a, b) \<in> set (ls @ (x1, sep) # list)"
          have "set_btree x1 = set_btree sub \<union> {x}"
            using T_i sub_set by auto
          moreover have "x < sep"
            using False Node.prems a_split list_split local.Cons sorted_wrt_list_sorted split_fun_req(3) by fastforce
          ultimately have "sub_sep_cons (x1,sep)"
            using sub_list_cons by fastforce
          then show "sub_sep_cons (a, b)"
            using Node.prems \<open>(a, b) \<in> set (ls @ (x1, sep) # list)\<close> a_split list_split local.Cons split_fun_set(2) split_fun_set(3) by fastforce
        next
          fix sepa y
          assume "sepa \<in> set (seperators (ls@(x1,sep)#list))" "y \<in> set_btree t"
          then show "sepa < y" using set_seperators_split
            by (metis Node.prems a_split list_split local.Cons sorted_alt.simps(2) split_fun_req(1))
        next
          fix y assume "y \<in> set (subtrees (ls@(x1,sep)#list))"
          then show "sorted_alt y" using sub_sorted set_subtrees_split
            by (metis (mono_tags, lifting) Node.prems T_i Un_iff a_split ball_empty insertE list_split local.Cons sorted_alt.simps(2) sorted_up_i.simps(1) split_fun_req(1))
        next
          show "sorted_alt t"
            using Node.prems sorted_alt.simps(2) by simp
        qed
        then show ?thesis
          using Node a_split list_split Cons False T_i by simp
      next
        case (Up_i x21 x22 x23)
        have "sorted_alt (Node (ls@(x21,x22)#(x23,sep)#list) t)"
          unfolding sorted_alt.simps
        proof (safe)
          fix a b assume a_in_set: "(a, b) \<in> set (ls @ (x21, x22) # (x23, sep) # list)"
          have "set_btree x23 \<subseteq> set_btree sub \<union> {x}"
            using Up_i sub_set by auto
          moreover have "x < sep"
            using False Node.prems a_split list_split local.Cons sorted_wrt_list_sorted split_fun_req(3) by fastforce
          ultimately have "sub_sep_cons (x23, sep)"
            using sub_list_cons by fastforce
          moreover have "sub_sep_cons (x21,x22)" using sub_sorted Up_i by simp
          ultimately show "sub_sep_cons (a, b)" using a_in_set sub_list_cons
            by force
        next
          fix y assume "y \<in> set (subtrees (ls@(x21,x22)#(x23,sep)#list))"
          then show "sorted_alt y"
            using sub_sorted Up_i  set_subtrees_split[of ls x21 x22 "(x23,sep)#list"] set_subtrees_split
            list_split Node Cons
            by (metis (no_types, lifting) UnI1 Un_insert_right \<open>\<And>thesis. (\<And>sub sep. a = (sub, sep) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> fst_conv image_insert insertE list.simps(15) set_map sorted_alt.simps(2) sorted_up_i.simps(2) split_fun_req(1) subtrees.simps sup_bot.right_neutral)
        next
          show "sorted_alt t" using Node by simp
        next
          fix ty z assume assms:  "ty \<in> set_btree t" "z \<in> set (seperators (ls @ (x21, x22) # (x23, sep) # list))"
          then have "(z \<in> set (seperators ls) \<union> set (seperators list) \<union> {sep}) \<or> z = x22"
            using set_seperators_split by auto
          then show "z < ty"
          proof
            have "\<forall>y \<in> set_btree sub. y < ty" "x < ty"
              using Node.prems a_split assms(1) list_split local.Cons split_fun_set(1) sorted_wrt_list_sorted split_fun_req(3) by fastforce+
            moreover have "x22 \<in> set_btree sub \<union> {x}" using sub_set Up_i by auto
            ultimately have "x22 < ty" by blast
            moreover assume "z = x22"
            ultimately show "z < ty" by simp
          next
            assume "z \<in> set (seperators ls) \<union> set (seperators list) \<union> {sep}"
            then show "z < ty"
              by (metis Node.prems a_split assms(1) list_split local.Cons set_seperators_split sorted_alt.simps(2) split_fun_req(1))
          qed
        next
          have "sub_sep_sm (x21,x22) (x23,sep)"
          proof -
            have "\<forall>x \<in> set_btree x23. x22 < x"
              using Up_i sub_sorted by auto
              moreover have "x22 < sep"
                by (metis (no_types, lifting) False Node.prems Un_insert_right Up_i a_split case_prod_unfold insert_iff less_le list.simps(5) list_split local.Cons set_up_i.simps(2) snd_conv sorted_alt.simps(2) sorted_wrt_list_sorted split_fun_req(3) split_fun_set(1) sub_sep_cons.simps sub_set sup_bot.right_neutral)
              ultimately show ?thesis by simp
          qed
          moreover have "\<forall>y \<in> set ls. sub_sep_sm y (x21,x22)"
          proof -
            have "\<forall>y \<in> set ls. sub_sep_sm y (sub,sep)"
            using sorted_l_forall sub_lists_sorted(1)
            by metis
            show ?thesis
            proof
              fix y assume y_in_ls: "y \<in> set ls"
              then obtain ysub ysep where y_split: "y = (ysub, ysep)"
                by (meson surj_pair)
              then have "\<forall>z \<in> set_btree sub. ysep < z"
                using \<open>\<forall>y\<in>set ls. sub_sep_sm y (sub, sep)\<close> y_in_ls by auto
              moreover have "ysep < x"
                using Node.prems y_split y_in_ls list_split sorted_wrt_list_sorted split_fun_req(2) by fastforce
              ultimately have "\<forall>z \<in> set_btree x21. ysep < z" "ysep < x22"
                using Up_i sub_set by auto
              then show "sub_sep_sm y (x21, x22)"
                by (simp add: y_split)
            qed
          qed
          moreover have "\<forall>y \<in> set list. sub_sep_sm (x23,sep) y"
            using sorted_r_forall sub_lists_sorted(2)
            by auto
          ultimately show "sorted_wrt sub_sep_sm (ls @ (x21, x22) # (x23, sep) # list)"
            using sorted_wrt_split2 sorted_wrt_append sub_lists_sorted(1) sub_lists_sorted(2)
            by fastforce
        qed
        then show ?thesis using Node a_split list_split Cons False Up_i
          by (simp del: node_i.simps add: node_i_sorted)
      qed
    qed
  qed
qed simp

thm ins.induct
thm btree.induct

(* wrapped up insert invariants *)

lemma tree_i_bal: "bal_up_i u \<Longrightarrow> bal (tree_i u)"
  apply(cases u)
   apply(auto)
  done

lemma tree_i_order: "\<lbrakk>k > 0; root_order_up_i k u\<rbrakk> \<Longrightarrow> root_order k (tree_i u)"
  apply(cases u)
   apply(auto simp add: order_impl_root_order)
  done


lemma tree_i_sorted: "sorted_up_i u \<Longrightarrow> sorted_alt (tree_i u)"
  apply(cases u)
   apply(auto)
  done

lemma tree_i_set: "set_up_i u = set_btree (tree_i u)"
  apply(cases u)
   apply(auto)
  done

lemma insert_bal: "bal t \<Longrightarrow> bal (insert k x t)"
  using ins_bal
  by (simp add: tree_i_bal)

lemma insert_order: "\<lbrakk>k > 0; root_order k t\<rbrakk> \<Longrightarrow> root_order k (insert k x t)"
  using ins_root_order
  by (simp add: tree_i_order)

lemma insert_sorted: "sorted_alt t \<Longrightarrow> sorted_alt (insert k x t)"
  using ins_sorted
  by (simp add: tree_i_sorted)

lemma insert_set: "set_btree t \<union> {x} = set_btree (insert k x t)"
  using ins_set
  by (simp add: tree_i_set)

(* TODO how to specify the height invariant for the whole tree? *)


(* deletion *)

thm list.simps


fun rebalance_middle_tree where
"rebalance_middle_tree k ls Leaf sep rs Leaf = (
  Node (ls@(Leaf,sep)#rs) Leaf
)" |
"rebalance_middle_tree k ls (Node mts mt) sep rs (Node tts tt) = (
  if length mts \<ge> k \<and> length tts \<ge> k then 
    Node (ls@(Node mts mt,sep)#rs) (Node tts tt)
  else (
    case rs of [] \<Rightarrow> (
      case node_i k (mts@(mt,sep)#tts) tt of
       T_i u \<Rightarrow>
        Node ls u |
       Up_i l a r \<Rightarrow>
        Node (ls@[(l,a)]) r) |
    (Node rts rt,rsep)#rs \<Rightarrow> (
      case node_i k (mts@(mt,sep)#rts) rt of
      T_i u \<Rightarrow>
        Node (ls@(u,rsep)#rs) (Node tts tt) |
      Up_i l a r \<Rightarrow>
        Node (ls@(l,a)#(r,rsep)#rs) (Node tts tt))
))"


fun rebalance_last_tree where
"rebalance_last_tree k ts t = (
case last ts of (sub,sep) \<Rightarrow>
   rebalance_middle_tree k (butlast ts) sub sep [] t
)"

fun split_max where
"split_max k (Node ts t) = (case t of Leaf \<Rightarrow> (
  let (sub,sep) = last ts in 
    (Node (butlast ts) sub, sep)
)|
_ \<Rightarrow> 
case split_max k t of (sub, sep) \<Rightarrow>
  (rebalance_last_tree k ts sub, sep)
)"

fun del where
"del k x Leaf = Leaf" |
"del k x (Node ts t) = (
  case split_fun ts x of 
    (ls,[]) \<Rightarrow> 
     rebalance_last_tree k ls (del k x t)
  | (ls,(sub,sep)#rs) \<Rightarrow> (
      if sep \<noteq> x then 
        rebalance_middle_tree k ls (del k x sub) sep rs t
      else if sub = Leaf then
        Node (ls@rs) t
      else let (sub_s, max_s) = split_max k sub in
        rebalance_middle_tree k ls sub_s max_s rs t
  )
)"

fun reduce_root where
"reduce_root Leaf = Leaf" |
"reduce_root (Node ts t) = (case ts of
   [] \<Rightarrow> t |
   _ \<Rightarrow> (Node ts t)
)"


fun delete where "delete k x t = reduce_root (del k x t)"

thm node_i_height
find_theorems height

(* invariant for intermediate states at deletion
in particular we allow for an underflow to 0 subtrees *)
fun almost_order where
"almost_order k Leaf = True" |
"almost_order k (Node ts t) = (
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and>
   order k t
)"


lemma root_order_up_impl_almost_order: "\<lbrakk>k > 0; root_order k t\<rbrakk> \<Longrightarrow> almost_order k t"
  apply(cases t)
   apply(auto)
  done

lemma rebalance_middle_tree_height:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "height (rebalance_middle_tree k ls sub sep rs t) = height (Node (ls@(sub,sep)#rs) t)"
proof (cases "height t")
  case 0
  then have "t = Leaf" "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis by simp
next
  case (Suc nat)
  then obtain tts tt where t_node: "t = Node tts tt"
    using height_Leaf by (cases t) simp
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) simp
  then show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      then have "height_up_i (node_i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node_i_height by blast
      also have "\<dots> = max (height t) (height sub)"
        by (metis assms(1) height_up_i.simps(2) height_list_drop_eq sub_node t_node)
      finally have height_max: "height_up_i (node_i k (mts @ (mt, sep) # tts) tt) = max (height t) (height sub)" by simp
      then show ?thesis
        proof (cases "node_i k (mts@(mt,sep)#tts) tt")
          case (T_i u)
          then have "height u = max (height t) (height sub)" using height_max by simp
          then have "height (Node ls u) = height (Node (ls@[(sub,sep)]) t)" using height_btree_order height_btree_swap
            by (simp add: fold_max_max max.commute)
          then show ?thesis using Nil False T_i
            by (simp add: sub_node t_node)
        next
          case (Up_i l a r)
          then have "height (Node (ls@[(sub,sep)]) t) = Suc (fold max (map height (subtrees ls)) (max (height sub) (height t)))"
             by (simp add: fold_max_max)
          also have "\<dots> = Suc (fold max (map height (subtrees ls)) (max (height l) (height r)))"
            using height_max Up_i assms(1) by auto
          also have "\<dots> = height (Node (ls@[(l,a)]) r)" using fold_max_append by auto
          finally show ?thesis
            using Up_i local.Nil sub_node t_node by auto
        qed
    next
      case (Cons a list)
      then obtain rsub rsep where a_split: "a = (rsub, rsep)"
        by (cases a)
      then obtain rts rt where r_node: "rsub = Node rts rt"
        using assms(2) Cons height_Leaf Suc by (cases rsub) simp_all

      then have "height_up_i (node_i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node_i_height by blast
      also have "\<dots> = max (height rsub) (height sub)"
        by (metis r_node height_up_i.simps(2) height_list_drop_eq max.commute sub_node)
      finally have height_max: "height_up_i (node_i k (mts @ (mt, sep) # rts) rt) = max (height rsub) (height sub)" by simp
      then show ?thesis
      proof (cases "node_i k (mts@(mt,sep)#rts) rt")
        case (T_i u)
        then have "height u = max (height rsub) (height sub)"
          using height_max T_i by simp
        then have "fold max (map height (subtrees (ls@(u,rsep)#list))) = fold max (map height (subtrees (ls@(sub,sep)#rs)))"
          using Cons a_split subtrees_split set_eq_fold by auto
        then show ?thesis 
          using T_i False Cons r_node a_split sub_node t_node by auto
      next
        case (Up_i l a r)
        then have height_max: "max (height l) (height r) = max (height rsub) (height sub)" using height_max by auto

        (* TODO: this calculation may be significantly minimized by using sufficiently non-abstract lemmas *)
        have "fold max (map height (subtrees (ls@(sub,sep)#rs))) (height t) =
                   max (height sub) (fold max (map height (subtrees (ls@rs))) (height t))"
          using fold_max_extract by auto
        also have "\<dots> = max (height sub) (fold max (map height (subtrees (ls@(rsub,rsep)#list))) (height t))"
          using Cons a_split by auto
        also have "\<dots> = max (height sub) (max (height rsub) (fold max (map height (subtrees (ls@list))) (height t)))"
        proof -
          have "fold max (map height (subtrees (ls@(rsub,rsep)#list))) (height t)
= max (height rsub) (fold max (map height (subtrees (ls@list))) (height t))"
            using fold_max_extract by simp
          then show ?thesis by simp
        qed
        also have "\<dots> = max (max (height sub) (height rsub)) (fold max (map height (subtrees (ls@list))) (height t))"
          by auto
        also have "\<dots> = max (max (height l) (height r)) (fold max (map height (subtrees (ls@list))) (height t))"
          using height_max by simp
        also have "\<dots> = max (height l) (max (height r) (fold max (map height (subtrees (ls@list))) (height t)))"
          using height_max by simp
        also have "\<dots> = (fold max (map height ((subtrees ls)@l#r#(subtrees list))) (height t))"
        proof -
          have f1: "map height (subtrees ls) @ map height (map fst list) = map height (subtrees (ls @ list))"
            by simp
          have f2: "height r # map height (map fst list) = map height (r # subtrees list)"
            by simp
          have "map height (subtrees ls) @ height l # map height (r # subtrees list) = map height (subtrees ls @ l # r # subtrees list)"
            by simp
          then show ?thesis
            using f2 f1 by (metis (no_types) fold_max_extract)
        qed
        also have "\<dots> = fold max (map height (subtrees (ls@(l,a)#(r,rsep)#list))) (height t)" by auto
        finally show ?thesis
          using Cons a_split r_node Up_i sub_node t_node by auto
      qed
    qed
  qed (simp add: sub_node t_node)
qed


lemma rebalance_last_tree_height:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "height (rebalance_last_tree k ts t) = height (Node ts t)"
  using rebalance_middle_tree_height assms by auto

fun nonempty_lasttreebal where
"nonempty_lasttreebal Leaf = True" |
"nonempty_lasttreebal (Node ts t) = 
((\<exists>ls tsub tsep. ts = (ls@[(tsub,tsep)]) \<and> height tsub = height t)
\<and> nonempty_lasttreebal t)"

lemma split_max_height:
"\<lbrakk>split_max k t = (sub,sep); nonempty_lasttreebal t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow>
   height sub = height t"
proof(induction t arbitrary: k sub sep)
  case Node1: (Node tts tt)
  then obtain ls tsub tsep where tts_split: "tts = ls@[(tsub,tsep)]" by auto
  then show ?case
  proof (cases tt)
    case Leaf
    then have "height (Node (ls@[(tsub,tsep)]) tt) = max (height (Node ls tsub)) (Suc (height tt))"
      using height_btree_swap2 height_btree_order by metis
    moreover have "split_max k (Node tts tt) = (Node ls tsub, tsep)"
      using Leaf Node1 tts_split by auto
    ultimately show ?thesis
      using Leaf Node1 height_Leaf max_def by auto
  next
    case Node2: (Node x21 x22)
    then obtain subsub subsep where sub_split: "split_max k tt = (subsub,subsep)" by (cases "split_max k tt")
    then have "height subsub = height tt" using Node1 Node2 by auto
    moreover have "split_max k (Node tts tt) = (rebalance_last_tree k tts subsub, subsep)"
      using Node1 Node2 tts_split sub_split by auto
    ultimately show ?thesis using rebalance_last_tree_height Node1 Node2 by auto
  qed
qed auto

lemma order_bal_nonempty_lasttreebal: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> nonempty_lasttreebal t"
proof(induction k t rule: order.induct)
  case (2 k ts t)
  then have "length ts > 0" by auto
  then obtain ls tsub tsep where ts_split: "ts = (ls@[(tsub,tsep)])"
    by (metis eq_fst_iff length_greater_0_conv snoc_eq_iff_butlast)
  moreover have "height tsub = height t"
    using "2.prems"(3) ts_split by auto
  moreover have "nonempty_lasttreebal t" using 2 order_impl_root_order by auto
  ultimately show ?case by simp
qed simp

lemma bal_sub_height: "bal (Node (ls@a#rs) t) \<Longrightarrow> (case rs of [] \<Rightarrow> True | (sub,sep)#_ \<Rightarrow> height sub = height t)"
  by (cases rs) (auto)

lemma del_height: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> height (del k x t) = height t"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split_fun ts x = (ls, list)" by (cases "split_fun ts x")
  then show ?case
  proof(cases list)
    case Nil
    then have "height (del k x t) = height t"
      using 2 list_split order_bal_nonempty_lasttreebal
      by (simp add: order_impl_root_order)
    moreover obtain lls sub sep where "ls = lls@[(sub,sep)]"
      using split_fun_req(1) 2 list_split Nil
      by (metis append_Nil2 nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
    moreover have "Node ls t = Node ts t" using split_fun_req(1) Nil list_split by auto
    ultimately show ?thesis
      using rebalance_last_tree_height 2 list_split Nil split_fun_req(1) by auto
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_fun_req(1) by blast
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then have "sep \<noteq> x \<or> (sep = x \<and> sub = Leaf) \<or> (sep = x \<and> (\<exists>ts t. sub = Node ts t))"
      using height_btree.cases by auto
    then show ?thesis
    proof (elim disjE)
      assume asms: "sep \<noteq> x"
      have "height (del k x sub) = height t"
        using 2 \<open>sep \<noteq> x\<close> a_split list_split Cons split_fun_set(1)
        by (metis bal.simps(2) order_impl_root_order root_order.simps(2) some_child_sub(1))
      then have "height (rebalance_middle_tree k ls (del k x sub) sep rs t) = height (Node (ls@((del k x sub),sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) \<open>height (del k x sub) = height t\<close> a_split list_split local.Cons split_fun_set(1) by fastforce
      also have "\<dots> = height (Node ts t)"
        using 2 a_split asms list_split Cons split_fun_set(1) split_fun_req(1)
        by auto
      finally show ?thesis
        using asms Cons a_split list_split 2
        by simp
    next
      assume asms: "sep = x \<and> sub = Leaf"
      then have "height (Node ts t) = height (Node (ls@rs) t)"
        using bal_height
        using "2.prems"(3) a_split list_split Cons split_fun_req(1) by fastforce
      then show ?thesis
        using a_split list_split Cons asms 2 by auto
    next
      assume asms: "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      then obtain sts st where sub_node: "sub = Node sts st" by blast
      obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun_set(1) split_max_height sub_node)
      then have "height (rebalance_middle_tree k ls sub_s max_s rs t) = height (Node (ls@(sub_s,sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node ts t)"
        using 2 a_split asms list_split Cons split_fun_set(1) split_fun_req(1) \<open>height sub_s = height t\<close> by fastforce
      finally show ?thesis using asms Cons a_split list_split 2 sub_node sub_split
        by auto
    qed
  qed
qed simp

lemma rebalance_middle_tree_set:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "set_btree (rebalance_middle_tree k ls sub sep rs t) = set_btree (Node (ls@(sub,sep)#rs) t)"
proof(cases "height t")
  case 0
  then have "t = Leaf" "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis by simp
next
  case (Suc nat)
  then obtain tts tt where t_node: "t = Node tts tt"
    using height_Leaf by (cases t) simp
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) simp
  then show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      then have
        "set_up_i (node_i k (mts@(mt,sep)#tts) tt) = set_btree (Node (mts@(mt,sep)#tts) tt)"
        using node_i_set by (simp del: node_i.simps)
      then show ?thesis 
        by (cases "node_i k (mts@(mt,sep)#tts) tt") (auto simp add: t_node sub_node set_btree_split False Nil)
    next
      case (Cons r list)
      then obtain rsub rsep where r_split[simp]:"r = (rsub,rsep)" by (cases r)
      then obtain rts rt where rsub_split[simp]: "rsub = Node rts rt"
        using assms Cons height_Leaf Suc by (cases rsub) simp
      then have
        "set_up_i (node_i k (mts@(mt,sep)#rts) rt) = set_btree (Node (mts@(mt,sep)#rts) rt)"
        using node_i_set by (simp del: node_i.simps)
      then show ?thesis 
        by (cases "node_i k (mts@(mt,sep)#rts) rt")
           (auto simp add: t_node sub_node set_btree_split False Cons)
    qed
  qed (simp add: t_node sub_node)
qed


lemma rebalance_last_tree_set:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "set_btree (rebalance_last_tree k ts t) = set_btree (Node ts t)"
  using rebalance_middle_tree_set assms by auto

find_theorems butlast last

lemma split_max_set:
  "\<lbrakk>split_max k t = (sub,sep); nonempty_lasttreebal t; t \<noteq> Leaf\<rbrakk> \<Longrightarrow>
   set_btree t = set_btree sub \<union> {sep}"
proof(induction t arbitrary: k sub sep)
  case Node1: (Node ts t)
  then obtain ls tsub tsep where ts_split: "ts = ls@[(tsub,tsep)]" by auto
  then show ?case
  proof (cases t)
    case Leaf
    then show ?thesis
      using Node1 Leaf ts_split by fastforce
  next
    case Node2: (Node x21 x22)
    then obtain subsub subsep where sub_split: "split_max k t = (subsub,subsep)" by (cases "split_max k t")
    then have "set_btree subsub \<union> {subsep} = set_btree t" using Node1 Node2 by auto
    then have "set_btree (rebalance_last_tree k ts subsub) \<union> {subsep} = set_btree (Node ts t)"
      using rebalance_last_tree_set split_max_height Node1 Node2
      by (metis (no_types, lifting) Un_insert_right btree.distinct(1) nonempty_lasttreebal.simps(2) rebalance_last_tree_set set_btree_split(2) sub_split sup_bot.right_neutral)
    moreover have "split_max k (Node ts t) = (rebalance_last_tree k ts subsub, subsep)"
      using Node1 Node2 ts_split sub_split by auto
    ultimately show ?thesis using rebalance_last_tree_set Node1 Node2 by auto
  qed
qed auto

lemma sorted_left_right:
  assumes "sorted_wrt sub_sep_sm ts"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "split_fun ts x = (l,r)"
    and "\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree t. sep < y"
  shows "\<forall>y \<in> set_btree_list l. y < x"
    and "case r of [] \<Rightarrow> True | a#rs \<Rightarrow> (\<forall>y \<in> set_btree_list rs. y > x) \<and> (\<forall>y \<in> set_btree t. y > x)"
proof -
  show "\<forall>y\<in>set_btree_list l. y < x"
  proof
    fix y assume asms: "y \<in> set_btree_list l"
    then obtain a where a_set: "a \<in> set l \<and> y \<in> set_btree_pair a" by auto
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then have sep_sm: "sep < x"
      using \<open>a = (sub, sep)\<close> a_set assms(1) assms(3) sorted_wrt_list_sorted split_fun_req(2) by fastforce   
    then show "y < x"
      using a_set a_split assms(2) assms(3) sep_sm sorted_wrt_sorted_right split_fun_req(1) by fastforce
  qed
next
  show "case r of [] \<Rightarrow> True | a#rs \<Rightarrow> (\<forall>y \<in> set_btree_list rs. y > x) \<and> (\<forall>y \<in> set_btree t. y > x)"
  proof (cases r)
    case (Cons b rs)
    then obtain sub sep where "b = (sub,sep)" by (cases b)
    then have "sep \<ge> x"
      using assms(1) assms(3) local.Cons sorted_wrt_list_sorted split_fun_req(3) by fastforce
    moreover have "\<forall>y \<in> set_btree_list rs. y > sep" 
    proof 
      fix y assume asms: "y \<in> set_btree_list rs"
      then obtain a where a_set: "a \<in> set rs \<and> y \<in> set_btree_pair a" by auto
      then obtain asub asep where a_split: "a = (asub,asep)" by (cases a)
      then have "y \<in> set_btree asub \<or> y = asep" using asms a_set by auto
      then show "y > sep"
      proof
        assume "y \<in> set_btree asub"
        then show "sep < y"
          by (metis \<open>b = (sub, sep)\<close> a_set a_split assms(1) assms(3) local.Cons some_child_sub(1) sorted_wrt_append sorted_wrt_sorted_left split_fun_req(1))
      next
        assume "y = asep"
        then show "sep < y"
          by (metis \<open>b = (sub, sep)\<close> a_set a_split assms(1) assms(3) local.Cons sorted_r_forall sorted_wrt_append split_fun_req(1) sub_sep_sm.simps)
      qed
    qed
    moreover have "\<forall>y \<in> set_btree t. y > sep"
      using \<open>b = (sub, sep)\<close> assms(3) assms(4) local.Cons split_fun_set(1) by fastforce
    ultimately show ?thesis
      using Cons by fastforce
  qed simp
qed

lemma sorted_split_contains:
  assumes "sorted_wrt sub_sep_sm ts"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "(\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree t. sep < y)"
    and "split_fun ts x = (l,r)"
  shows "x \<notin> set_btree_list l"
    and "case r of [] \<Rightarrow> True | a#rs \<Rightarrow> x \<notin> set_btree_list rs \<and> x \<notin> set_btree t"
proof
  show "x \<in> set_btree_list l \<Longrightarrow> False" using assms sorted_left_right by blast
next
  show "case r of [] \<Rightarrow> True | a#rs \<Rightarrow> x \<notin> set_btree_list rs \<and> x \<notin> set_btree t"
    using assms sorted_left_right
    by (metis (no_types, lifting) list.case_eq_if not_less_iff_gr_or_eq)  
qed

lemma del_set: "\<lbrakk>k > 0; root_order k t; bal t; sorted_alt t\<rbrakk> \<Longrightarrow> set_btree (del k x t) = set_btree t - {x}"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split_fun ts x = (ls, list)" by (cases "split_fun ts x")
then have "\<forall>sep \<in> set (seperators ls). sep < x"
      by (meson "2.prems"(4) list_split sorted_alt.simps(2) sorted_wrt_list_sorted split_fun_req(2))
  then show ?case
  proof(cases list)
    case Nil
    then obtain lls sub sep where ls_last: "ls = lls@[(sub,sep)]"
      using split_fun_req(1) 2
      by (metis append_Nil2 list_split nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
    
    have "set_btree (del k x t) = set_btree t - {x}"
      using 2 Nil list_split
      by (simp add: order_impl_root_order)
    moreover have "x \<notin> set_btree_list ls" using sorted_split_contains
       "2.prems"(4) list_split sorted_alt.simps(2) by blast
    ultimately have "set_btree (Node ls t) - {x} = set_btree (Node ls (del k x t))"
      by auto
    also have "\<dots> = set_btree (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_set 2 list_split Nil del_height ls_last
      by (metis append_Nil2 bal.simps(2) nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) split_fun_req(1))
    finally show ?thesis unfolding del.simps using Nil 2 list_split
      by (metis (no_types, lifting) append_Nil2 case_prod_conv list.simps(4) split_fun_req(1))
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_fun_req(1) by blast
    from Cons list_split have x_not_sub: "x \<notin> set_btree_list rs" "x \<notin> set_btree_list ls" "x \<notin> set_btree t"
      using sorted_split_contains 2
        by (metis list.simps(5) sorted_alt.simps(2))+
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then have "sep \<noteq> x \<or> (sep = x \<and> sub = Leaf) \<or> (sep = x \<and> (\<exists>ts t. sub = Node ts t))"
      using height_btree.cases by auto
    then show ?thesis
    proof (elim disjE)
      assume asms: "sep \<noteq> x"
      have sub_height: "height (del k x sub) = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) list_split local.Cons order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun.del_height split_fun_axioms split_fun_set(1))
      from asms have sub_set: "set_btree (del k x sub) = set_btree sub - {x}"
        by (metis "2.IH"(2) "2.prems" a_split bal.simps(2) list_split local.Cons order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_alt.simps(2) split_fun_set(1))
      have "set_btree (rebalance_middle_tree k ls (del k x sub) sep rs t) = 
            set_btree (Node (ls@(del k x sub,sep)#rs) t)"
        using rebalance_middle_tree_set rs_height sub_height by simp
      also have "\<dots> = set_btree_list ls \<union> set_btree (del k x sub) \<union> {sep} \<union> set_btree_list rs \<union> set_btree t"
        using set_btree_split by auto
      also have "\<dots> = (set_btree_list ls \<union> set_btree sub \<union> {sep} \<union> set_btree_list rs \<union> set_btree t) - {x}"
        using sorted_split_contains asms x_not_sub sub_set by blast
      also have "\<dots> = set_btree (Node (ls@(sub,sep)#rs) t) - {x}"
        by auto
      finally show ?thesis unfolding del.simps
        using a_split asms list_split local.Cons split_fun_req(1) by force
    next
      assume asms: "(sep = x \<and> sub = Leaf)"
      then have "set_btree (Node (ls@rs) t) = set_btree_list ls \<union> set_btree_list rs \<union> set_btree t"
        using set_btree_split by simp
      also have "\<dots> = (set_btree_list ls \<union> set_btree_list rs \<union> set_btree t) - {x}"
        using x_not_sub by simp
      also have "\<dots> = (set_btree_list ls \<union> {x} \<union> {} \<union> set_btree_list rs \<union> set_btree t) - {x}"
        by simp
      also have "\<dots> = set_btree (Node (ls@(Leaf,x)#rs) t) - {x}"
        using set_btree_split by simp
      finally show ?thesis unfolding del.simps
        using a_split asms list_split local.Cons split_fun_req(1) by force
    next
      assume asms: "(sep = x \<and> (\<exists>ts t. sub = Node ts t))"
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      from asms 2 have "x \<notin> set_btree sub"
        by (metis a_split list_split local.Cons not_less_iff_gr_or_eq sorted_alt.simps(2) split_fun_set(1) sub_sep_cons.simps)
      obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have set_sub: "set_btree sub = set_btree sub_s \<union> {max_s}"
        using split_max_set
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun.split_fun_set(1) split_fun_axioms sub_node)

      from sub_split have "height sub_s = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun_set(1) split_max_height sub_node)
      then have "set_btree (rebalance_middle_tree k ls sub_s max_s rs t) =
                 (set_btree (Node (ls@(sub_s,max_s)#rs) t))"
        using rebalance_middle_tree_set
        by (metis "2.prems"(3) bal_sub_height list_split local.Cons split_fun_req(1))
      also have "\<dots> = set_btree_list ls \<union> set_btree sub_s \<union> {max_s} \<union> set_btree_list rs \<union> set_btree t"
        using set_btree_split by auto
      also have "\<dots> = set_btree_list ls \<union> set_btree sub \<union> set_btree_list rs \<union> set_btree t"
        using set_sub by blast
      also have "\<dots> = (set_btree_list ls \<union> set_btree sub \<union> set_btree_list rs \<union> set_btree t) - {x}"
        using x_not_sub \<open>x \<notin> set_btree sub\<close> by auto
       also have "\<dots> = (set_btree_list ls \<union> set_btree sub \<union> {x} \<union> set_btree_list rs \<union> set_btree t) - {x}"
        by simp
      also have "\<dots> = set_btree (Node (ls@(sub,x)#rs) t) - {x}"
        using set_btree_split by auto
      also have "\<dots> = set_btree (Node ts t) - {x}"
        using asms Cons a_split list_split split_fun_req(1) by auto
      finally show ?thesis unfolding del.simps
        using asms Cons a_split list_split sub_node sub_split by auto
    qed
  qed
qed simp

find_theorems node_i bal_up_i

lemma height_bal_subtrees_merge: "\<lbrakk>height (Node as a) = height (Node bs b); bal (Node as a); bal (Node bs b)\<rbrakk>
 \<Longrightarrow> \<forall>x \<in> set (subtrees as) \<union> {a}. height x = height b"
  by (metis Suc_inject Un_iff bal.simps(2) height_bal_tree singletonD)

lemma height_bal_node_i: 
  assumes "height (Node as a) = height (Node bs b)"
    and "bal (Node as a)"
    and "bal (Node bs b)"
  shows "bal_up_i (node_i k (as@(a,x)#bs) b)"
proof -
  have "\<forall>x\<in>set (subtrees (as @ (a, x) # bs)). bal x"
    using subtrees_split assms by auto
  moreover have "bal b"
    using assms by auto
  moreover have "\<forall>x\<in>set (subtrees as) \<union> {a} \<union> set (subtrees bs). height x = height b"
    using assms height_bal_subtrees_merge
    by blast
  ultimately show ?thesis using node_i_bal[of "as@(a,x)#bs"] by (auto simp del: node_i.simps)
qed

lemma rebalance_middle_tree_bal: "bal (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> bal (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case t_node: (Node tts tt)
  assume assms: "bal (Node (ls @ (sub, sep) # rs) t)"
  then obtain mts mt where sub_node: "sub = Node mts mt"
    by (cases sub) (auto simp add: t_node)
  have sub_heights: "height sub = height t" "bal sub" "bal t"
    using assms by auto
  show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
  case False
  then show ?thesis
    proof (cases rs)
      case Nil
      have "height_up_i (node_i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node_i_height by blast
      also have "\<dots> = Suc (height tt)"
        by (metis height_bal_tree height_up_i.simps(2) height_list_drop_eq max.idem sub_heights(1) sub_heights(3) sub_node t_node)
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up_i (node_i k (mts@(mt,sep)#tts) tt) = height t" by simp
      moreover have "bal_up_i (node_i k (mts@(mt,sep)#tts) tt)"
        using height_bal_node_i sub_node t_node sub_heights by auto
      ultimately show ?thesis
        apply (cases "node_i k (mts@(mt,sep)#tts) tt")
        using assms local.Nil sub_node t_node by auto
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t" "bal rsub"
        using assms local.Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "height_up_i (node_i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node_i_height by blast
      also have "\<dots> = Suc (height rt)"
        by (metis Un_iff  \<open>height rsub = height t\<close> assms bal.simps(2) bal_split height_bal_tree height_up_i.simps(2) height_list_drop_eq list.set_intros(1) local.Cons max.idem r_node r_split set_append some_child_sub(1) sub_heights(1) sub_node)
      also have "\<dots> = height rsub"
        using height_bal_tree r_node rsub_height(2) by fastforce
      finally have 1: "height_up_i (node_i k (mts@(mt,sep)#rts) rt) = height rsub" by simp
      moreover have 2: "bal_up_i (node_i k (mts@(mt,sep)#rts) rt)"
        using height_bal_node_i sub_node sub_heights rsub_height r_node by auto
      ultimately show ?thesis
      proof (cases "node_i k (mts@(mt,sep)#rts) rt")
        case (T_i u)
        then have "bal (Node (ls@(u,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_btree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False T_i
          by (auto simp del: node_i.simps bal.simps)
      next
        case (Up_i l a r)
        then have "bal (Node (ls@(l,a)#(r,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_btree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False Up_i
          by (auto simp del: node_i.simps bal.simps)
      qed
    qed
  qed
qed (simp add: height_Leaf)

find_theorems last butlast

lemma rebalance_last_tree_bal: "\<lbrakk>bal (Node ts t); ts \<noteq> []\<rbrakk> \<Longrightarrow> bal (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_bal append_butlast_last_id[of ts]
  apply(cases "last ts") 
  apply(auto simp del: bal.simps rebalance_middle_tree.simps)
  done


lemma split_max_bal: "\<lbrakk>split_max k t = (s_sub,s_max); bal t; t \<noteq> Leaf; nonempty_lasttreebal t\<rbrakk>
\<Longrightarrow> bal s_sub"
proof(induction k t arbitrary: s_sub s_max rule: split_max.induct)
case (1 k ts t)
  then show ?case
    proof (cases t)
      case Leaf
      then obtain sub sep where last_split: "last ts = (sub,sep)" using 1 by auto
      then have "height sub = height t" using 1 by auto
      then have "bal (Node (butlast ts) sub)" using 1 last_split by auto
      then show ?thesis using 1 Leaf last_split by auto
    next
      case (Node tts tt)
      then obtain sub sep where t_split: "split_max k t = (sub,sep)" by (cases "split_max k t")
      then have "height sub = height t" using 1 Node
        by (metis btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height)
      then have "bal (Node ts sub)" using 1 t_split Node by auto
      then show ?thesis
        using rebalance_last_tree_bal t_split Node 1
        by (auto simp del: bal.simps rebalance_middle_tree.simps)
    qed
  qed simp

lemma del_bal: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> bal (del k x t)"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls,rs)" by (cases "split_fun ts x")
  then show ?case
  proof (cases rs)
    case Nil
    then have "bal (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order)
    moreover have "height (del k x t) = height t"
      using 2 del_height by (simp add: order_impl_root_order)
    moreover have "ts \<noteq> []" using 2 by auto
    ultimately have "bal (rebalance_last_tree k ts (del k x t))"
      using 2 Nil order_bal_nonempty_lasttreebal rebalance_last_tree_bal
      by simp
    then have "bal (rebalance_last_tree k ls (del k x t))" 
      using list_split split_fun_req(1) Nil by fastforce
    then show ?thesis
      using 2 list_split Nil
      by auto
  next
    case (Cons r rs)
    then obtain sub sep where r_split: "r = (sub,sep)" by (cases r)
    then have sub_height: "height sub = height t" "bal sub"
      using 2 Cons list_split split_fun_set(1) by fastforce+
    then have "sep \<noteq> x \<or> (sep = x \<and> sub = Leaf) \<or> (sep = x \<and> (\<exists>ts t. sub = Node ts t))"
      using height_btree.cases by auto
    then show ?thesis
    proof (elim disjE)
      assume asms: "sep \<noteq> x"
      then have "bal (del k x sub)" "height (del k x sub) = height sub" using sub_height
        using "2.IH"(2) "2.prems"(2) list_split local.Cons r_split split_fun_set(1) order_impl_root_order
        apply (metis "2.prems"(1) root_order.simps(2) some_child_sub(1))
        by (metis "2.prems"(1) "2.prems"(2) list_split local.Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun.del_height split_fun_axioms split_fun_set(1) sub_height(2))
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split local.Cons r_split split_fun_req(1) by blast
      ultimately have "bal (Node (ls@(del k x sub,sep)#rs) t)"
        using bal_substitute2[of ls sub sep rs t "del k x sub"] by metis
      then have "bal (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_bal[of ls "del k x sub" sep rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split asms by auto
    next
      assume "sep = x \<and> sub = Leaf"
      moreover have "bal (Node (ls@rs) t)"
        using bal_split list_split split_fun_req(1) r_split
        by (metis "2.prems"(3) local.Cons)
      ultimately show ?thesis
        using 2 list_split Cons r_split by auto
    next
      assume asms: "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height sub"
        using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_height(2) sub_node)
      moreover have "bal sub_s"
        using split_max_bal
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_height(2) sub_node sub_split)
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split local.Cons r_split split_fun_req(1) by blast
      ultimately have "bal (Node (ls@(sub_s,sep)#rs) t)"
        using bal_substitute2[of ls sub sep rs t "sub_s"] by metis
      then have "bal (Node (ls@(sub_s,max_s)#rs) t)"
        using bal_substitute3 by metis
      then have "bal (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_bal[of ls sub_s max_s rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split asms sub_node sub_split by auto
    qed
  qed
qed simp


lemma rebalance_middle_tree_order:
  assumes "almost_order k sub"
    and "\<forall>s \<in> set (subtrees (ls@rs)). order k s" "order k t"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof(cases t)
  case Leaf
  then have "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis using Leaf assms by auto
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "order_up_i k (node_i k (mts@(mt,sep)#tts) tt)"
        using node_i_order[of k "mts@(mt,sep)#tts" tt] assms(1,3) t_node sub_node
        by (auto simp del: order_up_i.simps node_i.simps)
      then show ?thesis
        apply(cases "node_i k (mts@(mt,sep)#tts) tt")
        using assms t_node sub_node False Nil apply (auto simp del: node_i.simps)
        done
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t"
        using assms local.Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "order_up_i k (node_i k (mts@(mt,sep)#rts) rt)"
        using node_i_order[of k "mts@(mt,sep)#rts" rt] assms(1,2) t_node sub_node r_node r_split Cons
        by (auto simp del: order_up_i.simps node_i.simps)
        then show ?thesis        
        apply(cases "node_i k (mts@(mt,sep)#rts) rt")
        using assms t_node sub_node False Cons r_split r_node apply (auto simp del: node_i.simps)
        done
    qed
  qed
qed

(* we have to proof the order invariant once for an underflowing last tree *)
lemma rebalance_middle_tree_last_order:
  assumes "almost_order k t"
    and  "\<forall>s \<in> set (subtrees (ls@(sub,sep)#rs)). order k s"
    and "rs = []"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case Leaf
  then have "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis using Leaf assms by auto
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    have "order_up_i k (node_i k (mts@(mt,sep)#tts) tt)"
        using node_i_order[of k "mts@(mt,sep)#tts" tt] assms t_node sub_node
        by (auto simp del: order_up_i.simps node_i.simps)
    then show ?thesis
      apply(cases "node_i k (mts@(mt,sep)#tts) tt")
      using assms t_node sub_node False Nil apply (auto simp del: node_i.simps)
      done
  qed
qed

lemma rebalance_last_tree_order:
  assumes "ts = ls@[(sub,sep)]"
    and "\<forall>s \<in> set (subtrees (ts)). order k s" "almost_order k t"
    and "length ts \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_last_order assms by auto

lemma split_max_order: 
  "\<lbrakk>order k t; t \<noteq> Leaf; split_max k t = (sub,sep); nonempty_lasttreebal t\<rbrakk> \<Longrightarrow> almost_order k sub"
proof(induction k t arbitrary: sub sep rule: split_max.induct)
  case (1 k ts t)
  then obtain ls sub sep where ts_not_empty: "ts = ls@[(sub,sep)]"
    by auto
  then show ?case
  proof (cases t)
    case Leaf
    then show ?thesis using ts_not_empty 1 by auto
  next
    case (Node)
    then obtain s_sub s_max where sub_split: "split_max k t = (s_sub, s_max)"
      by (cases "split_max k t")
    moreover have "height sub = height s_sub"
      by (metis "1.prems"(4) Node Pair_inject append1_eq_conv btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height sub_split ts_not_empty)
    ultimately have "almost_order k (rebalance_last_tree k ts s_sub)"
      using rebalance_last_tree_order[of ts ls sub sep k s_sub] 1 ts_not_empty Node sub_split by auto
    then show ?thesis
      using Node 1 sub_split by auto
  qed
qed simp

lemma subtrees_split2: "set (subtrees (l@r)) = set (subtrees l) \<union> set (subtrees r)"
  apply(induction r)
   apply(auto)
  done

lemma del_order: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> almost_order k (del k x t)"
proof (induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split_fun ts x = (ls, list)" by (cases "split_fun ts x")
  then show ?case
  proof (cases list)
    case Nil
    then have "almost_order k (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order)
    moreover obtain lls lsub lsep where ls_split: "ls = lls@[(lsub,lsep)]"
      using 2 Nil list_split
      by (metis eq_snd_iff length_greater_0_conv rev_exhaust root_order.simps(2) split_fun.split_fun_length_l split_fun_axioms)
    moreover have "height t = height (del k x t)" using del_height 2 by (simp add: order_impl_root_order)
    moreover have "length ls = length ts"
      using Nil list_split split_fun_length_l by auto
    ultimately have "almost_order k (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_order[of ls lls lsub lsep k "del k x t"]
      by (metis "2.prems"(2) "2.prems"(3) Un_iff append_Nil2 bal.simps(2) list_split local.Nil root_order.simps(2) singletonI split_fun_req(1) subtrees_split)
    then show ?thesis
      using 2 list_split Nil by auto 
  next
    case (Cons r rs)
    
    from Cons obtain sub sep where r_split: "r = (sub,sep)" by (cases r)

    have inductive_help:
      "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t"
      "\<forall>s\<in>set (subtrees (ls @ rs)). order k s"
      "Suc (length (ls @ rs)) \<le> 2 * k"
      "order k t"
      using Cons "2.prems"(3) bal_sub_height list_split split_fun_req(1) apply (blast)
      using subtrees_split2 2 list_split split_fun_req(1) Cons r_split subtrees_split
        apply (metis Un_iff root_order.simps(2))
      using "2"(4) list_split local.Cons r_split split_fun_length apply auto
      done

    from r_split have "sep \<noteq> x \<or> (sep = x \<and> sub = Leaf) \<or> (sep = x \<and> (\<exists>ts t. sub = Node ts t))"
      using height_btree.cases by auto
    then show ?thesis 
    proof (elim disjE)
      assume assms: "sep \<noteq> x"
      then have "almost_order k (del k x sub)" using 2 list_split Cons r_split order_impl_root_order
        by (metis bal.simps(2) root_order.simps(2) some_child_sub(1) split_fun_set(1))
      moreover have "height (del k x sub) = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) list_split local.Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun.del_height split_fun_axioms split_fun_set(1))
      ultimately have "almost_order k (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_order[of k "del k x sub" ls rs t sep]
        using inductive_help
        using Cons r_split assms list_split by auto
      then show ?thesis using 2 Cons r_split assms list_split by auto
    next
      assume assms: "sep = x \<and> sub = Leaf"
      then have "almost_order k (Node (ls@rs) t)" using inductive_help by auto
      then show ?thesis using 2 Cons r_split assms list_split by auto
    next
      assume assms: "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t" using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_node)
      moreover have "almost_order k sub_s" using split_max_order
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun.split_fun_set(1) split_fun_axioms sub_node sub_split)
      ultimately have "almost_order k (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_order[of k sub_s ls rs t max_s] inductive_help
        by auto
      then show ?thesis
        using 2 Cons r_split list_split assms sub_split by auto
    qed
  qed
qed simp

(* TODO sortedness of delete *)

find_theorems sorted_alt
find_theorems sorted_wrt sub_sep_sm
find_theorems set seperators

lemma subtree_in_subtrees: "a \<in> set (subtrees (ls @ (a, b) # rs))"
  by simp

lemma subtree_sub_sm:
assumes "\<forall>x \<in> set_btree (Node tts tt). a < x"
    and "(c,d) \<in> set tts"
  shows "a < d"
    and "\<forall>y \<in> set_btree c. a < y"
  using assms apply (meson seperators_in_set some_child_sub(2) subsetD)
  using assms apply fastforce
  done

lemma sorted_sub_sep_impl: "sorted_alt (Node (ls @ (sub, sep) # rs) t) \<Longrightarrow> \<forall>y \<in> set_btree t. sep < y"
  by simp

lemma rebalance_middle_tree_sorted:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "sorted_alt (Node (ls@(sub,sep)#rs) t)"
  shows "sorted_alt (rebalance_middle_tree k ls sub sep rs t)"
proof(cases "height t")
  case 0
  then have "t = Leaf" "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis using assms by simp
next
  case (Suc nat)
  then obtain tts tt where t_node: "t = Node tts tt"
    using height_Leaf by (cases t) simp
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) simp

  have sub_sorted_lr:
    "sorted_wrt sub_sep_sm ls" 
    "sorted_wrt sub_sep_sm rs"
    "\<forall>x \<in> set ls. sub_sep_cons x"
    "\<forall>x \<in> set rs. sub_sep_cons x"
    using assms(3) sorted_alt.simps(2) sorted_alt_split_ls apply blast
    using assms(3) sorted_alt.simps(2) sorted_alt_split_rs apply blast
    using assms(3) by auto
  then show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "sorted_alt (Node (mts@(mt,sep)#tts) tt)" unfolding sorted_alt.simps
        using assms(3) sub_node t_node
      proof (safe)
        show "sorted_wrt sub_sep_sm (mts @ (mt, sep) # tts)"
          unfolding sorted_wrt_split
        proof(safe)
          show "sorted_wrt sub_sep_sm mts" "sorted_wrt sub_sep_sm tts"
            using assms sub_node t_node by auto
        next
          fix a b assume "(a, b) \<in> set mts"
          then show "sub_sep_sm (a, b) (mt, sep)"
            using subtree_in_subtrees 
            by (metis (no_types) Un_iff assms(3) list.set_intros(1) seperators_in_set set_append some_child_sub(2) sorted_alt.simps(2) sub_node sub_sep_cons.simps sub_sep_sm.simps subsetD)
        next
          fix a b assume "(a, b) \<in> set tts"
          then have "sep < b" "\<forall>y \<in> set_btree a. sep < y"
            using subtree_sub_sm assms t_node sorted_sub_sep_impl
            by metis+
          then show "sub_sep_sm (mt, sep) (a, b)"
            using subtree_in_subtrees assms
            by simp
        qed
      next
        fix a b assume "(a, b) \<in> set (mts @ (mt, sep) # tts)"
        show "sub_sep_cons (a,b)"
          by (metis (no_types, lifting) Un_iff \<open>(a, b) \<in> set (mts @ (mt, sep) # tts)\<close> assms(3) insert_iff list.set(2) set_append set_btree_split(2) sorted_alt.simps(2) sub_node sub_sep_cons.simps subtree_in_subtrees t_node)
      next
        fix x assume "x \<in> set_btree tt"
        then have x_in_t: "x \<in> set_btree t" by (simp add: t_node)
        fix sepa assume "sepa \<in> set (seperators (mts @ (mt, sep) # tts))"
        then have "sepa \<in> set (seperators mts) \<or> sepa = sep \<or> sepa \<in> set (seperators tts)"
          using set_seperators_split by auto
        then show "sepa < x" using x_in_t
          apply (elim disjE)
            apply (metis (no_types, lifting) Un_iff assms(3) dual_order.strict_trans list.set_intros(1) seperators_in_set set_append sorted_alt.simps(2) sorted_sub_sep_impl sub_node sub_sep_cons.simps subsetD)
            using assms(3) sorted_sub_sep_impl apply blast
            using \<open>x \<in> set_btree tt\<close> assms(3) sorted_alt.simps(2) t_node apply blast
            done
        qed auto
      then have
        sorted_node_i: "sorted_up_i (node_i k (mts@(mt,sep)#tts) tt)"
        using node_i_sorted by blast
     
      have "set_up_i (node_i k (mts@(mt,sep)#tts) tt) = set_btree (Node (mts@(mt,sep)#tts) tt)"
        using node_i_set by blast
      also have "\<dots> = set_btree sub \<union> set_btree t \<union> {sep}"
        using  sub_node t_node by auto
      finally have set_node_i: "set_up_i (node_i k (mts@(mt,sep)#tts) tt) = set_btree sub \<union> set_btree t \<union> {sep}"
        by simp
      then show ?thesis
      proof (cases "node_i k (mts@(mt,sep)#tts) tt")
        case (T_i u)
        have "sorted_alt (Node ls u)"
          unfolding sorted_alt.simps
          using assms T_i sorted_node_i sorted_wrt_append sub_sorted_lr
        proof (safe)
          fix lsep assume "lsep \<in> set (seperators ls)"
          fix x assume "x \<in> set_btree u"
          then have "x \<in> set_btree t \<or> x \<in> set_btree sub \<or> x = sep"
            using set_node_i T_i by auto
          then show "lsep < x"
            apply(elim disjE)
            using \<open>lsep \<in> set (seperators ls)\<close> assms(3) apply simp
            using \<open>lsep \<in> set (seperators ls)\<close> assms(3) sorted_alt.simps(2) sorted_alt_split_ls apply blast
            using \<open>lsep \<in> set (seperators ls)\<close> assms(3) sorted_alt_split_ls apply blast
            done
        qed auto
        then show ?thesis
          using T_i assms(3) local.Nil sub_node t_node by auto
      next
        case (Up_i l a r)
        then have set_lar:
          "set_btree l \<subseteq> set_btree sub \<union> set_btree t \<union> {sep}"
          "a \<in> set_btree sub \<union> set_btree t \<union> {sep}"
          "set_btree r \<subseteq> set_btree sub \<union> set_btree t \<union> {sep}"
          using set_node_i by auto
        have "sorted_alt (Node (ls@[(l,a)]) r)"
          unfolding sorted_alt.simps
        using Up_i sorted_node_i assms proof(safe)
          show "sorted_wrt sub_sep_sm (ls @ [(l, a)])"
            unfolding sorted_wrt_split
            apply (safe)
               apply (simp_all)
            using assms(3) sorted_alt.simps(2) sorted_alt_split_ls apply blast
          proof
            fix asub asep assume ls_split: "(asub,asep) \<in> set ls"
            then show "asep < a" using set_lar assms
              by (metis UnE Un_iff Un_iff insert_absorb insert_iff insert_not_empty set_append some_child_sub(2) sorted_alt.simps(2) sorted_alt_split_ls)
            show "\<forall>x \<in> set_btree l. asep < x"
              using set_lar assms ls_split
              proof -
                { fix aa :: 'a
                  have ff2: "asep \<in> set (seperators ls)"
                    by (meson ls_split some_child_sub(2))
                  have ff3: "\<And>a A aa Aa. (a::'a) \<notin> A \<or> a \<in> Set.insert aa (A \<union> Aa)"
                    by blast
                  have ff4: "sorted_alt (Node ls sub)"
                    using assms(3) sorted_alt_split_ls by blast
                  { assume "aa \<noteq> sep"
                    moreover
                    { assume "aa \<in> set_btree t"
                      then have "\<exists>ps b. sorted_alt (Node ps b) \<and> aa \<in> set_btree b \<and> asep \<in> set (seperators ps)"
                        using ff3 ff2 by (metis (no_types) Un_insert_right assms(3) set_seperators_split sup_bot.right_neutral) }
                    ultimately have "(aa \<notin> set_btree l \<or> asep < aa) \<or> (\<exists>ps b. sorted_alt (Node ps b) \<and> aa \<in> set_btree b \<and> asep \<in> set (seperators ps))"
                      using ff4 ff2 set_lar(1) by blast
                    then have "aa \<notin> set_btree l \<or> asep < aa"
                      using sorted_alt.simps(2) by blast }
                  then have "aa \<notin> set_btree l \<or> asep < aa"
                    using ff2 assms(3) sorted_alt_split_ls by blast }
                then show ?thesis
                  by blast
              qed
            qed
          next
            fix lsub lsep assume "(lsub, lsep) \<in> set (ls @ [(l, a)])"
            then have "(lsub, lsep) \<in> set ls \<or> (lsub,lsep) = (l,a)"
              by auto
            then show "sub_sep_cons (lsub, lsep)"
              apply(elim disjE)
              using assms(3) sorted_alt.simps(2) sorted_alt_split_ls apply blast
              using Up_i sorted_node_i by auto
          next
            fix sep assume "sep \<in> set (seperators (ls @ [(l, a)]))"
            then have "sep \<in> set (seperators ls) \<or> sep = a"
              by auto
            then have "\<forall>x \<in> set_btree r. sep < x"
              apply(elim disjE)
              using set_lar assms
               apply (metis (no_types, lifting) Un_iff Un_insert_right dual_order.strict_trans insert_iff sorted_alt.simps(2) sorted_alt_split_ls sorted_sub_sep_impl subsetD sup_bot.right_neutral)
              using sorted_node_i Up_i
               apply simp
              done
            then show "\<And>x. x \<in> set_btree r \<Longrightarrow> sep < x"
              by simp
          qed auto
        then show ?thesis
          using False Up_i local.Nil sub_node t_node by auto
      qed
    next
      case (Cons r list)
      then obtain rsub rsep where r_split[simp]:"r = (rsub,rsep)" by (cases r)
      then obtain rts rt where rsub_split[simp]: "rsub = Node rts rt"
        using assms Cons height_Leaf Suc by (cases rsub) simp
      then have
        "set_up_i (node_i k (mts@(mt,sep)#rts) rt) = set_btree (Node (mts@(mt,sep)#rts) rt)"
        using node_i_set by (simp del: node_i.simps)
      then show ?thesis 
        by (cases "node_i k (mts@(mt,sep)#rts) rt")
           (auto simp add: t_node sub_node set_btree_split False Cons)
    qed
  qed (simp add: t_node sub_node assms)
qed

lemma reduce_root_order: "\<lbrakk>k > 0; almost_order k t\<rbrakk> \<Longrightarrow> root_order k (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits simp add: order_impl_root_order)
  done

lemma reduce_root_bal: "bal t \<Longrightarrow> bal (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits)
  done

thm set_btree_split

lemma reduce_root_set: "set_btree t = set_btree (reduce_root t)"
  apply(cases t)
  apply(simp)
  subgoal for ts t
    apply(cases ts)
     apply(auto)
    done
  done


lemma delete_order: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> root_order k (delete k x t)"
  using del_order
  by (simp add: reduce_root_order)

lemma delete_bal: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> bal (delete k x t)"
  using del_bal
  by (simp add: reduce_root_bal)

lemma delete_set: "\<lbrakk>k > 0; bal t; root_order k t; sorted_alt t\<rbrakk> \<Longrightarrow> set_btree (delete k x t) = set_btree t - {x}"
  using del_set
  by (metis reduce_root_set split_fun.delete.elims split_fun_axioms)


(* TODO runtime wrt runtime of split_fun *)

(* TODO (opt) proof of max/min filling/height of btree (is this related to ins/del functions at all?)
 filling \<Rightarrow> follows directly from order constraints 
 height \<Rightarrow> interesting *)

(* TODO simpler induction schemes /less boilerplate isabelle/src/HOL/ex/Induction_Schema *)

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