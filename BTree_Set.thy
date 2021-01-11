theory BTree_Set
  imports BTree
begin


fun split_half:: "('a btree\<times>'a) list \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
  "split_half xs = (take (length xs div 2) xs, drop (length xs div 2) xs)"


lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma split_half_not_empty: "length xs \<ge> 1 \<Longrightarrow> \<exists>ls sub sep rs. split_half xs = (ls,(sub,sep)#rs)"
  using drop_not_empty
  by (metis (no_types, hide_lams) drop0 drop_eq_Nil eq_snd_iff hd_Cons_tl le_trans not_one_le_zero split_half.simps)



(* TODO way to use this for custom case distinction? *)
lemma node_i_cases: "length xs \<le> k \<or> (\<exists>ls sub sep rs. split_half xs = (ls,(sub,sep)#rs))"
proof -
  have "\<not> length xs \<le> k \<Longrightarrow> length xs \<ge> 1"
    by linarith
  then show ?thesis
    using split_half_not_empty
    by blast
qed

(* proof obligation for termination proofs containing the split function *)
lemma subtree_smaller: "sub \<in> set (subtrees xs) \<Longrightarrow> 
      size sub < Suc (size_list (\<lambda>x. Suc (size (fst x))) xs)"
  apply(induction xs)
   apply(simp_all)
  using image_iff by fastforce


locale split_fun =
  fixes split_fun ::  "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)"
  assumes split_fun_req:
    "\<lbrakk>split_fun xs p = (ls,rs)\<rbrakk> \<Longrightarrow> ls @ rs = xs"
    "\<lbrakk>split_fun xs p = (ls,rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (separators ls). p > sep"
    "\<lbrakk>split_fun xs p = (ls,rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> case rs of [] \<Rightarrow> True | (sub,sep)#rrs \<Rightarrow> p \<le> sep"
begin

thm split_fun_req


lemma split_fun_drule:
  assumes "split_fun ts p = (ls,rs)"
    and "sorted_less (separators ts)"
  shows "ls@rs = ts"
    and "\<forall>sep \<in> set (separators ls). p > sep"
    and "case rs of [] \<Rightarrow> True | (sub,sep)#rrs \<Rightarrow> p \<le> sep"
  using split_fun_req assms by auto

lemma split_fun_req3_alt: 
  assumes "split_fun xs p = (ls,rs)"
    and "sorted_less (separators xs)"
  shows "case rs of [] \<Rightarrow> True | (_,rsep)#rrs \<Rightarrow> p \<le> rsep \<and> (\<forall>sep \<in> set (separators rrs). p < sep)"
proof (cases rs)
  case (Cons a rrs)
  moreover obtain rsub rsep where a_pair: "(rsub, rsep) = a"
    by (metis surj_pair)
  moreover from assms have "sorted_less (separators rs)"
    by (metis map_append sorted_wrt_append split_fun_axioms split_fun_def)
  ultimately have "\<forall>rrsep \<in> set (separators rrs). rsep < rrsep"
    by auto
  moreover have "p \<le> rsep"
    using a_pair assms(1) assms(2) local.Cons split_fun_req(3)
    by fastforce
  ultimately show ?thesis
    using Cons a_pair
    by auto
qed simp

lemmas split_fun_req_alt = split_fun_req(1) split_fun_req(2) split_fun_req3_alt




lemma split_fun_length_l: "split_fun ts x = (l,[]) \<Longrightarrow> length l = length ts"
  using split_fun_req_alt by fastforce

lemma split_fun_length: "split_fun ts x = (ls, (a, b) # rs) \<Longrightarrow> Suc(length ls + length rs) = length ts"
  using split_fun_req_alt by fastforce

lemma split_fun_set: 
  assumes "split_fun ts z = (l,(a,b)#r)"
  shows "(a,b) \<in> set ts"
    and "(x,y) \<in> set l \<Longrightarrow> (x,y) \<in> set ts"
    and "(x,y) \<in> set r \<Longrightarrow> (x,y) \<in> set ts"
    and "set l \<union> set r \<union> {(a,b)} = set ts"
    and "\<exists>x \<in> set ts. b \<in> Basic_BNFs.snds x"
  using split_fun_req_alt assms by fastforce+


lemma [termination_simp]:"(ls, (sub, sep) # rs) = split_fun t y \<Longrightarrow>
      size sub < Suc (size_list (\<lambda>x. Suc (size (fst x))) t  + size l)"
  by (metis group_cancel.add1 plus_1_eq_Suc some_child_sub(1) split_fun_set(1) subtree_smaller trans_less_add1)

subsection "isin Function"

fun isin:: "'a btree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin (Leaf) y = False" |
  "isin (Node ts t) y = (
  case split_fun ts y of (_,rs) \<Rightarrow>
   (case rs of
   (sub,sep)#_ \<Rightarrow>
    (if y = sep
        then True
        else isin sub y
    )
   | [] \<Rightarrow> isin t y))"

(* proofs *)
(* showing that isin implies the set containment is easy *)

lemma "isin t x \<Longrightarrow> x \<in> set_btree t"
  apply(induction t)
  using split_fun_axioms apply(auto split!: list.splits if_splits dest!: split_fun_set(1))
   apply force+
  done

(* explicit proof *)
lemma isin_impl_set: "isin n x \<Longrightarrow> x \<in> set_btree n"
proof(induction n x rule: isin.induct)
  case (2 ts t x)
  then obtain ls rs where list_split[simp]: "split_fun ts x = (ls,rs)" by auto
  then have "rs \<noteq> [] \<or> (rs = [] \<and> isin t x)"
    using 2
    by auto
  then show ?case
  proof
    assume "rs \<noteq> []"
    then obtain sub sep list where rs_split[simp]: "rs = (sub,sep)#list"
      by (cases rs) auto
    then show "x \<in> set_btree (Node ts t)"
    proof (cases "x = sep")
      assume "x = sep"
      then have "x \<in> set (separators ts)"
        by (metis list_split rs_split some_child_sub(2) split_fun_set(1))
      then show "x \<in> set_btree (Node ts t)"
        by (metis set_btree_induct)
    next
      assume "x \<noteq> sep"
      then have "x \<in> set_btree sub"
        using 2 by auto
      then show "x \<in> set_btree (Node ts t)"
        by (metis list_split rs_split child_subset fst_eqD split_fun_set(1) subsetD)
    qed
  qed (auto simp add: "2.IH")
qed simp


(* from the split_fun axioms, we may follow the isin requirements *)
lemma split_fun_separator_match:
  assumes "sorted_less (separators xs)" 
    and "x \<in> set (separators xs)" 
    and "split_fun xs x = (ls,rs)"
  shows "snd (hd rs) = x"
    and "rs \<noteq> []"
proof -
  have "x \<in> set (separators (ls@rs))"
    using assms split_fun_req_alt(1)
    by blast
  also have "x \<notin> set (separators ls)"
    using assms(1,3) split_fun_req_alt(2)
    by blast
  ultimately have "x \<in> set (separators rs)"
    by simp
  then show "rs \<noteq> []"
    by auto
  then obtain psub psep list where rs_split[simp]: "rs = (psub, psep)#list"
    by (cases rs) auto
  then have "(\<forall>y \<in> set (separators list). x < y)"
    using split_fun_req_alt(3)[of xs x ls rs] assms Cons
    by auto
  then have "x = psep"
    using \<open>x \<in> set (separators rs)\<close>
    by auto
  then show "snd (hd rs) = x"
    by auto
qed


lemma split_fun_subtree_match:
  assumes "\<exists>sub \<in> set (subtrees xs). x \<in> set_btree sub"
    and "sorted_wrt sub_sep_sm xs"
    and "\<forall>x \<in> set xs. sub_sep_cons x"
    and "split_fun xs x = (ls,rs)"
  shows "x \<in> set_btree (fst (hd rs))"
    and "rs \<noteq> []"
proof -
  have "\<forall> sep \<in> set (separators ls). sep < x"
    using assms(2,4) split_fun_req_alt(2) sorted_wrt_list_sorted
    by fastforce
  then have "\<forall> (sub, sep) \<in> set ls. x \<notin> set_btree sub"
    by (metis (no_types, lifting) Un_iff assms(3,4) case_prodI2 not_less_iff_gr_or_eq set_append some_child_sub(2) split_fun_req_alt(1) sub_sep_cons.simps)
  moreover have "\<exists>sub \<in> set (subtrees (ls@rs)). x \<in> set_btree sub"
    using assms(1,4) split_fun_req_alt(1)
    by blast
  ultimately have "\<exists>sub \<in> set (subtrees rs). x \<in> set_btree sub"
    by auto
  then show "rs \<noteq> []"
    by auto
  then obtain psub psep list where rs_split[simp]: "rs = (psub,psep)#list"
    by (metis eq_snd_iff hd_Cons_tl)
  then have "x \<le> psep"
    using  split_fun_req_alt(3)[of xs x ls rs] assms Cons sorted_wrt_list_sorted
    by fastforce
  moreover have "\<forall>t \<in> set (subtrees list). \<forall>x \<in> set_btree t. psep < x"
    using sorted_wrt_sorted_left rs_split assms(2,4) split_fun_req_alt(1) sorted_wrt_append sorted_wrt_list_sorted
    by blast
  ultimately have "\<forall>t \<in> set (subtrees list). x \<notin> set_btree t"
    using leD
    by blast
  then have "x \<in> set_btree psub"
    using \<open>\<exists>sub\<in>set (subtrees rs). x \<in> set_btree sub\<close>
    by auto
  then show "x \<in> set_btree (fst (hd rs))"
    by simp
qed

(* Additional proof for last tree *)
lemma split_fun_last_empty: 
  assumes "x \<in> set_btree t"
    and "(\<forall>sep \<in> set (separators ts). \<forall>y \<in> set_btree t. sep < y)"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "sorted_less (separators ts)"
    and "split_fun ts x = (ls,rs)"
  shows "rs = []"
proof (cases rs)
  case (Cons r list)
  then obtain sub sep where r_pair: "r = (sub,sep)"
    by (cases r)
  then have "x \<le> sep" 
    using assms split_fun_req_alt Cons r_pair
    by fastforce
  then have "False"
    by (metis r_pair assms(1,2,5) leD Cons some_child_sub(2) split_fun_set(1))
  then show ?thesis
    by simp
qed simp


lemma set_impl_isin: "sorted_btree t \<Longrightarrow> x \<in> set_btree t \<Longrightarrow> isin t x"
proof (induction t x rule: isin.induct)
  case (2 ts t x)
  obtain ls rs where list_split: "split_fun ts x = (ls,rs)"
    by fastforce
  from 2 have "x \<in> set (separators ts) \<or> (\<exists>sub \<in> set (subtrees ts). x \<in> set_btree sub) \<or> x \<in> set_btree t"
    by (meson set_btree_induct)
  then show ?case
  proof (elim disjE)
    assume assms: "x \<in> set (separators ts)"
    then have "snd (hd rs) = x" "rs \<noteq> []"
      using list_split split_fun_separator_match assms 2 sorted_wrt_list_sorted
      by (metis sorted_btree.simps(2))+
    then show "isin (Node ts t) x"
      using list_split
      by (cases rs) auto
  next
    assume assms: "(\<exists>sub \<in> set (subtrees ts). x \<in> set_btree sub)"
    then have "x \<in> set_btree (fst (hd rs))" "rs \<noteq> []"
      using list_split split_fun_subtree_match "2.prems"(1) assms
      by auto
    moreover have "fst (hd rs) \<in> set (subtrees ts)"
      using calculation(2) list_split split_fun_req_alt(1)
      by fastforce
    ultimately show "isin (Node ts t) x" 
      using 2 list_split
      unfolding isin.simps
      by (cases rs) (fastforce)+
  next
    assume assms: "x \<in> set_btree t"
    then have "rs = []" 
      using split_fun_last_empty "2.prems"(1) list_split
      using sorted_btree.simps(2) sorted_wrt_list_sorted
      by blast
    then show "isin (Node ts t) x"
      using "2.IH"(1) "2.prems"(1) assms list_split
      by auto
  qed
qed auto

lemma isin_set: "sorted_btree t \<Longrightarrow> isin t y = (y \<in> set_btree t)"
  using isin_impl_set set_impl_isin
  by fastforce

corollary isin_set_inorder: "sorted_less (inorder t) \<Longrightarrow> isin t y = (y \<in> set (inorder t))"
  by (simp add: isin_set set_inorder_btree sorted_btree_eq)


(* TODO time proof *)

(*
fun t_isin:: "'a btree \<Rightarrow> 'a \<Rightarrow> nat" where
 "t_isin (Leaf) y = 0" |
 "t_isin (Node ts t) y = t_split_fun ts y + 1 + (case split_fun ts y of (_,r) \<Rightarrow> (case r of (sub,sep)#_ \<Rightarrow> 1 + (if y = sep then 0 else t_isin sub y) | [] \<Rightarrow> t_isin t y))"


lemma "\<lbrakk>k > 0; order k t; bal t\<rbrakk> \<Longrightarrow> t_isin t x \<le> (height t)*(2+(t_split_fun_wc (2*k)))"
  oops
*)


subsection "insert Function"


datatype 'b up_i = T_i "'b btree" | Up_i "'b btree" 'b "'b btree"


(* this function merges two nodes and returns separately split nodes
   if an overflow occurs *)

fun node_i:: "nat \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> 'a btree \<Rightarrow> 'a up_i" where
  "node_i k xs x = (
  if length xs \<le> 2*k then T_i (Node xs x)
  else (
    case split_half xs of (ls, (sub,sep)#rs) \<Rightarrow>
      Up_i (Node ls sub) sep (Node rs x)
    )
  )"


fun ins:: "nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a up_i" where
  "ins k x Leaf = (Up_i Leaf x Leaf)" |
  "ins k x (Node ts t) = (
  case split_fun ts x of
    (ls,(sub,sep)#rs) \<Rightarrow> 
      (if sep = x then
        T_i (Node ts t)
      else
        (case ins k x sub of 
          Up_i l a r \<Rightarrow>
             node_i k (ls @ (l,a)#(r,sep)#rs) t | 
          T_i a \<Rightarrow>
            T_i (Node (ls @ (a,sep) # rs) t))) |
    (ls, []) \<Rightarrow>
      (case ins k x t of
         Up_i l a r \<Rightarrow>
           node_i k (ls@[(l,a)]) r |
         T_i a \<Rightarrow>
           T_i (Node ls a)
  )
)"



fun tree_i::"'a up_i \<Rightarrow> 'a btree" where
  "tree_i (T_i sub) = sub" |
  "tree_i (Up_i l a r) = (Node [(l,a)] r)"

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree_i (ins k x t)"

(* proofs *)

fun order_up_i where
  "order_up_i k (T_i sub) = order k sub" |
  "order_up_i k (Up_i l a r) = (order k l \<and> order k r)"

fun root_order_up_i where
  "root_order_up_i k (T_i sub) = root_order k sub" |
  "root_order_up_i k (Up_i l a r) = (order k l \<and> order k r)"


lemma node_i_root_order:
  assumes "length ts > 0"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "root_order_up_i k (node_i k ts t)"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by simp
next
  case False
  then obtain ls sub sep rs where split_half_ts: 
    "take (length ts div 2) ts = ls"
    "drop (length ts div 2) ts = (sub,sep)#rs" 
    using split_half_not_empty[of ts]
    by auto
  then have length_rs: "length rs = length ts - (length ts div 2) - 1"
    using length_drop
    by (metis One_nat_def add_diff_cancel_right' list.size(4))
  also have "\<dots> \<le> 4*k - ((4*k + 1) div 2)"
    using assms(2) by simp
  also have "\<dots> = 2*k"
    by auto
  finally have "length rs \<le> 2*k"
    by simp
  moreover have "length rs \<ge> k" 
    using False length_rs by simp
  moreover have "set ((sub,sep)#rs) \<subseteq> set ts"
    by (metis split_half_ts(2) set_drop_subset)
  ultimately have o_r: "order k sub" "order k (Node rs t)"
    using split_half_ts assms by auto
  moreover have "length ls \<ge> k"
    using length_take assms split_half_ts False
    by auto
  moreover have  "length ls \<le> 2*k"
    using assms(2) split_half_ts
    by auto
  ultimately have o_l: "order k (Node ls sub)"
    using set_take_subset assms split_half_ts
    by fastforce
  from o_r o_l show ?thesis
    by (simp add: False split_half_ts)
qed

lemma node_i_order_helper:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "case (node_i k ts t) of T_i t \<Rightarrow> order k t | _ \<Rightarrow> True"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by simp
next
  case False
  then obtain sub sep rs where 
    "drop (length ts div 2) ts = (sub,sep)#rs" 
    using split_half_not_empty[of ts]
    by auto
  then show ?thesis
    using assms by auto
qed


lemma node_i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "order_up_i k (node_i k ts t)"

  apply(cases "node_i k ts t")
  using node_i_root_order node_i_order_helper assms apply fastforce
  apply (metis node_i_root_order assms(2,3,4) le0 length_greater_0_conv list.size(3) node_i.simps order_up_i.simps(2) root_order_up_i.simps(2) up_i.distinct(1))
  done



(* "Automatic proof", using a number of lemmata 


lemma xs_split_fun_prop: 
  "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> P a"
 (* "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> \<forall>x \<in> set ls. P (fst x)"
  "\<lbrakk>\<forall>x \<in> set xs. P (fst x); split_fun xs x = (ls, (a, b) # rs)\<rbrakk> \<Longrightarrow> \<forall>x \<in> set rs. P (fst x)"*)
  using split_fun_req_alt(1) by fastforce+


lemma length_lemma:
"split_fun ts x = (ls, (a,b)#rs) \<Longrightarrow> length (ls@(a,b)#rs) = length (ls@(c,d)#(e,f)#rs) - 1"
"split_fun ts x = (ls, (a,b)#rs) \<Longrightarrow> length (ls@rs) = length (ls@(a,b)#rs) - 1"
  by auto

lemma help_lem:
  assumes  "\<forall>x \<in> set ls. P (fst x)" "\<forall>x \<in> set rs. P (fst x)"
    and "P a" "P c"
  shows "\<forall>x \<in> set (ls@(a,b)#(c,d)#rs). P (fst x)"
  using assms by(auto)

lemma ins_order_alt: "order k t \<Longrightarrow> order_up_i k (ins k x t)"
  apply(induction k x t rule: ins.induct)
   apply(auto simp del: node_i.simps split!: prod.splits list.splits up_i.splits
 simp add: split_fun_length_l split_fun_length split_fun_set_l split_fun_set node_i_order xs_split_fun_prop
split_fun_req_alt(1) length_lemma node_i_order[of "_" "_@(_,_)#(_,_)#_" "_"])
  subgoal for k x ts t x1 a b a l aa x2
  proof -
    assume assms:
    "(\<And>y. False \<Longrightarrow> y = [] \<Longrightarrow> order_up_i k (ins k x t))"
    "(\<And>xa y aa ba aa xb ya.
        xa = x1 \<and> aa = a \<and> ba = b \<and> aa = a \<Longrightarrow>
        y = (a, b) # a \<Longrightarrow> xb = a \<and> ya = b \<Longrightarrow> order k l \<and> order k x2)"
    "k \<le> length ts"
    "length ts \<le> 2 * k"
    "\<forall>x\<in>set ts. order k (fst x)"
    "order k t"
    "split_fun ts x = (x1, (a, b) # a)"
    "ins k x a = Up_i l aa x2"
    "b \<noteq> x"
    then have "k \<le> length (x1 @ (l, aa) # (x2, b) # a)" using split_fun_req_alt(1) length_lemma by auto
    moreover have "length (x1@(l,aa)#(x2,b)#a) \<le> 4*k+1" using split_fun_req_alt(1) length_lemma assms by auto
    moreover have "\<forall>x \<in> set (x1@(l,aa)#(x2,b)#a). order k (fst x)" using assms
      using split_fun_set by auto
    moreover have "order k t" using assms by auto
    ultimately show "order_up_i k (node_i k (x1 @ (l, aa) # (x2, b) # a) t)" using node_i_order[of k "_@(_,_)#(_,_)#_" t] by (auto simp del: node_i.simps)
  qed
  done *)

(* explicit proof *)
lemma ins_order: 
  "order k t \<Longrightarrow> order_up_i k (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split_fun ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_fun_req_alt(1)
    by simp

  show ?case
  proof (cases rs)
    case Nil
    then have "order_up_i k (ins k x t)"
      using 2 split_res
      by simp
    then show ?thesis
      using Nil 2 split_app split_res Nil node_i_order
      by (auto split!: up_i.splits simp del: node_i.simps)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using 2 a_prod Cons split_res
        by simp
    next
      case False
      then have "order_up_i k (ins k x sub)"
        using 2 split_res a_prod Cons split_fun_set(1) split_fun_axioms
        by fastforce
      then show ?thesis
        using 2 split_app Cons length_append node_i_order a_prod split_res
        by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp


(* notice this is almost a duplicate of ins_order *)
lemma ins_root_order: 
  assumes "root_order k t"
  shows "root_order_up_i k (ins k x t)"
proof(cases t)
  case (Node ts t)
  then obtain ls rs where split_res: "split_fun ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_fun_req_alt(1)
    by fastforce

  show ?thesis
  proof (cases rs)
    case Nil
    then have "order_up_i k (ins k x t)" using Node assms split_res
      by (simp add: ins_order)
    then show ?thesis
      using Nil Node split_app split_res assms node_i_root_order
      by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using assms Node a_prod Cons split_res
        by simp
    next
      case False
      then have "order_up_i k (ins k x sub)"
        using Node assms split_res a_prod Cons split_fun_set(1) split_fun_axioms
        by (metis ins_order root_order.simps(2) some_child_sub(1))
      then show ?thesis
        using assms split_app Cons length_append Node node_i_root_order a_prod split_res
        by (auto split!: up_i.splits simp del: node_i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp



fun height_up_i where
  "height_up_i (T_i t) = height t" |
  "height_up_i (Up_i l a r) = max (height l) (height r)"


lemma height_list_split: "height_up_i (Up_i (Node ls a) b (Node rs t)) = height (Node (ls@(a,b)#rs) t) "
  by (auto simp add: fold_max_max max.commute)

lemma node_i_height: "height_up_i (node_i k ts t) = height (Node ts t)"
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls, (sub, sep) # rs)"
    by (meson node_i_cases)
  then have "node_i k ts t = Up_i (Node (take (length ts div 2) ts) (sub)) sep (Node rs t)"
    using False by simp
  then show ?thesis
    using split_half_ts
    by (metis append_take_drop_id height_list_split snd_conv split_half.simps)
qed simp


fun bal_up_i where
  "bal_up_i (T_i t) = bal t" |
  "bal_up_i (Up_i l a r) = (height l = height r \<and> bal l \<and> bal r)"

lemma bal_list_split: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal_up_i (Up_i (Node ls a) b (Node rs t))"
  unfolding bal_up_i.simps
  by (metis bal_split_last(1) bal_split_right bal_split_left height_bal_tree)

lemma node_i_bal:
  assumes "\<forall>x \<in> set (subtrees ts). bal x"
    and "bal t"
    and "\<forall>x \<in> set (subtrees ts). height t = height x"
  shows "bal_up_i (node_i k ts t)"
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls, (sub, sep) # rs)"
    by (meson node_i_cases)
  then have "Up_i (Node (take (length ts div 2) ts) (sub)) sep (Node rs t) = node_i k ts t"
    using False by simp
  then show ?thesis
    using split_half_ts
    by (metis append_take_drop_id assms(1) assms(2) assms(3) bal.simps(2) bal_list_split snd_conv split_half.simps)
qed (simp add: assms)


lemma height_up_i_merge: "height_up_i (Up_i l a r) = height t \<Longrightarrow> height (Node (ls@(t,x)#rs) tt) = height (Node (ls@(l,a)#(r,x)#rs) tt)"
proof -
  assume "height_up_i (Up_i l a r) = height t"
  then have "height (Node (ls@(t,x)#rs) tt) = max (Suc (max (height l) (height r))) (height (Node (ls@rs) tt))"
    using fold_max_extract
    by auto
  also have "\<dots> = Suc (max (height l) (fold max (map height ((subtrees ls)@r#(subtrees rs))) (height tt)))"
    by (simp add: fold_max_max)
  also have "\<dots> = Suc (fold max (map height ((subtrees ls)@l#r#(subtrees rs))) (height tt))"
    by (metis (no_types, lifting) fold_max_extract list.simps(9) map_append)
  also have "\<dots> = height (Node (ls@(l,a)#(r,x)#rs) tt)"
    by auto
  finally show ?thesis
    by simp
qed



lemma ins_height: "height_up_i (ins k x t) = height t"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_list: "split_fun ts x = (ls,rs)"
    by (meson surj_pair)
  then have split_append: "ls@rs = ts"
    using split_fun_req_alt(1)
    by auto
  then show ?case
  proof (cases rs)
    case Nil
    then have height_sub: "height_up_i (ins k x t) = height t"
      using 2 by (simp add: split_list)
    then show ?thesis
    proof (cases "ins k x t")
      case (T_i a)
      then have "height (Node ts t) = height (Node ts a)"
        using height_sub
        by simp
      then show ?thesis
        using T_i Nil split_list split_append
        by simp
    next
      case (Up_i l a r)
      then have "height (Node ls t) = height (Node (ls@[(l,a)]) r)"
        using height_btree_order height_sub
        by (simp add: fold_max_max)
      then show ?thesis using 2 Nil split_list Up_i split_append
        by (simp del: node_i.simps add: node_i_height)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using Cons a_split 2 split_list
        by (simp del: height_btree.simps)
    next
      case False
      then have height_sub: "height_up_i (ins k x sub) = height sub"
        by (metis "2.IH"(2) a_split Cons split_list)
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i a)
        then have "height a = height sub"
          using height_sub by auto
        then have "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@(a,sep)#rs) t)"
          by auto
        then show ?thesis 
          using T_i height_sub False Cons 2 split_list a_split split_append
          by auto
      next
        case (Up_i l a r)
        then have "height (Node (ls@(sub,sep)#list) t) = height (Node (ls@(l,a)#(r,sep)#list) t)"
          using height_up_i_merge height_sub
          by fastforce
        then show ?thesis
          using Up_i False Cons 2 split_list a_split split_append
          by (auto simp del: node_i.simps simp add: node_i_height)
      qed
    qed
  qed
qed simp


(* the below proof is overly complicated as a number of lemmas regarding height are missing *)
lemma ins_bal: "bal t \<Longrightarrow> bal_up_i (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split_fun ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_fun_req_alt(1)
    by fastforce

  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis 
    proof (cases "ins k x t")
      case (T_i a)
      then have "bal (Node ls a)" unfolding bal.simps
        by (metis "2.IH"(1) "2.prems" append_Nil2 bal.simps(2) bal_up_i.simps(1) height_up_i.simps(1) ins_height local.Nil split_app split_res)
      then show ?thesis 
        using Nil T_i 2 split_res
        by simp
    next
      case (Up_i l a r)
      then have 
        "(\<forall>x\<in>set (subtrees (ls@[(l,a)])). bal x)"
        "(\<forall>x\<in>set (subtrees ls). height r = height x)"
        using 2 Up_i Nil split_res split_app
        by simp_all (metis height_up_i.simps(2) ins_height max_def)
      then show ?thesis unfolding ins.simps
        using Up_i Nil 2 split_res
        by (simp del: node_i.simps add: node_i_bal)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using a_prod 2 split_res Cons by simp
    next
      case False
      then have "bal_up_i (ins k x sub)" using 2 split_res
        by (metis BTree.bal.simps(2) a_prod Cons some_child_sub(1) split_fun_set(1))
      show ?thesis
      proof (cases "ins k x sub")
        case (T_i x1)
        then have  "height x1 = height t"
          by (metis "2.prems" BTree.bal.simps(2) T_i a_prod height_up_i.simps(1) ins_height Cons some_child_sub(1) split_fun_set(1) split_res)
        then show ?thesis
          using split_app Cons T_i 2 split_res a_prod
          by auto
      next
        case (Up_i l a r)
          (* The only case where explicit reasoning is required - likely due to the insertion of 2 elements in the list *)
        then have
          "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). bal x"
          using Up_i split_app Cons 2 \<open>bal_up_i (ins k x sub)\<close> by auto
        moreover have "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). height x = height t"
          using False Up_i split_app Cons 2 \<open>bal_up_i (ins k x sub)\<close> ins_height split_res a_prod
          by simp_all (metis "2.prems" bal.simps(2) bal_split_last(1) fst_conv height_up_i.simps(2) image_Un set_append set_map split_fun_set(1) sup.idem sup_nat_def)
        ultimately show ?thesis using Up_i Cons 2 split_res a_prod
          by (simp del: node_i.simps add: node_i_bal)
      qed
    qed
  qed
qed simp

(* ins acts as ins_list wrt inorder *)

fun inorder_up_i where
  "inorder_up_i (T_i t) = inorder t" |
  "inorder_up_i (Up_i l a r) = inorder l @ [a] @ inorder r"

(* "simple enough" to be automatically solved *)
lemma node_i_inorder: "inorder_up_i (node_i k ts t) = inorder (Node ts t)"
  apply(cases "length ts \<le> 2*k")
   apply (auto split!: list.splits)
    (* we want to only transform in one direction here.. *)
  supply R = sym[OF append_take_drop_id, of "map _ ts" "(length ts div 2)"]
  thm R
  apply(subst R)
  apply (simp del: append_take_drop_id add: take_map drop_map)
  done

corollary node_i_inorder_simps:
  "node_i k ts t = T_i t' \<Longrightarrow> inorder t' = inorder (Node ts t)"
  "node_i k ts t = Up_i l a r \<Longrightarrow> inorder l @ a # inorder r = inorder (Node ts t)"
   apply (metis inorder_up_i.simps(1) node_i_inorder)
  by (metis append_Cons inorder_up_i.simps(2) node_i_inorder self_append_conv2)


lemma ins_sorted_inorder: "sorted_less (inorder t) \<Longrightarrow> (inorder_up_i (ins k (x::('a::linorder)) t)) = ins_list x (inorder t)"
  apply(induction k x t rule: ins.induct)
  using split_fun_axioms apply (auto split!: prod.splits list.splits up_i.splits simp del: node_i.simps
      simp add:  node_i_inorder node_i_inorder_simps)
    (* from here on we prefer an explicit proof, showing how to apply the IH  *)
  oops


(* specialize ins_list_sorted since it is cumbersome to express
 "inorder_list ts" as "xs @ [a]" and always having to use the implicit properties of split_fun*)

lemma ins_list_split:
  assumes "split_fun ts x = (ls, rs)"
    and "sorted_less (inorder (Node ts t))"
  shows "ins_list x (inorder (Node ts t)) = inorder_list ls @ ins_list x (inorder_list rs @ inorder t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_fun_req(1))
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  moreover have "sep < x"
  proof -
    have "sep \<in> set (separators ls)"
      by (simp add: ls_tail_split)
    moreover have "sorted_less (separators ts)"
      using assms sorted_inorder_subsepsm sorted_wrt_list_sorted sorted_inorder_impl_list
      by auto
    ultimately show "sep < x"
      using split_fun_req(2) assms(1)
      by blast
  qed
  moreover have "sorted_less (inorder_list ls)"
    using assms sorted_wrt_append split_fun_req_alt(1) by fastforce
  ultimately show ?thesis using assms(2) split_fun_req(1)[OF assms(1)]
    using ins_list_sorted[of "inorder_list ls' @ inorder sub" sep]
    by auto
qed

lemma ins_list_split_right_general:
  assumes "split_fun ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder_list ts)"
    and "sep \<noteq> x"
  shows "ins_list x (inorder_list ((sub,sep)#rs) @ zs) = ins_list x (inorder sub) @ sep # inorder_list rs @ zs"
proof -
  from assms have "x < sep"
  proof -
    from assms have "sorted_less (separators ts)"
      by (simp add: sorted_inorder_list_subsepsm sorted_wrt_list_sorted)
    then show ?thesis
      using split_fun_req(3)
      using assms
      by fastforce
  qed
  moreover have "sorted_less (inorder_pair (sub,sep))"
    using assms set_btree_inorder sorted_inorder_list_subcons sorted_inorder_subtrees_induct sorted_pair_list split_fun_req_alt(1)
    by fastforce
  ultimately show ?thesis
    using ins_list_sorted[of "inorder sub" "sep"]
    by auto
qed

(* this fits the actual use cases better *)
corollary ins_list_split_right:
  assumes "split_fun ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder_list ts @ inorder t)"
    and "sep \<noteq> x"
  shows "ins_list x (inorder_list ((sub,sep)#rs) @ inorder t) = ins_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
  using assms sorted_wrt_append split_fun.ins_list_split_right_general split_fun_axioms by fastforce


(* a simple lemma, missing from the standard as of now *)
lemma ins_list_contains_idem: "sorted_less xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> ins_list x xs = xs"
  apply(induction xs)
   apply auto
  done

declare node_i.simps [simp del]
declare node_i_inorder [simp add]  

lemma ins_inorder: "sorted_less (inorder t) \<Longrightarrow> (inorder_up_i (ins k x t)) = ins_list x (inorder t)"
proof(induction k x t rule: ins.induct)
  case (1 k x)
  then show ?case by auto
next
  case (2 k x ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls,rs)"
    by (cases "split_fun ts x")
  then have list_conc: "ts = ls@rs"
    using split_fun.split_fun_req_alt(1) split_fun_axioms by blast
  then show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
    proof (cases "ins k x t")
      case (T_i a)
      then have IH:"inorder a = ins_list x (inorder t)"
        using "2.IH"(1) "2.prems" list_split local.Nil sorted_inorder_last
        by auto

      have "inorder_up_i (ins k x (Node ts t)) = inorder_list ls @ inorder a"
        using list_split T_i Nil by (auto simp add: list_conc)
      also have "\<dots> = inorder_list ls @ (ins_list x (inorder t))"
        by (simp add: IH)
      also have "\<dots> = ins_list x (inorder (Node ts t))"
        using ins_list_split
        using "2.prems" list_split Nil by auto
      finally show ?thesis .
    next
      case (Up_i l a r)
      then have IH:"inorder_up_i (Up_i l a r) = ins_list x (inorder t)"
        using "2.IH"(1) "2.prems" list_split local.Nil sorted_inorder_last by auto

      have "inorder_up_i (ins k x (Node ts t)) = inorder_list ls @ inorder_up_i (Up_i l a r)"
        using list_split Up_i Nil by (auto simp add: list_conc)
      also have "\<dots> = inorder_list ls @ ins_list x (inorder t)"
        using IH by simp
      also have "\<dots> = ins_list x (inorder (Node ts t))"
        using ins_list_split
        using "2.prems" list_split local.Nil by auto
      finally show ?thesis .
    qed
  next
    case (Cons h list)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)

    then have sorted_inorder_sub: "sorted_less (inorder sub)"
      using "2.prems" list_conc local.Cons sorted_inorder_impl_list sorted_inorder_subtrees_induct
      by blast
    then show ?thesis
    proof(cases "x = sep")
      case True
      then have "x \<in> set (inorder (Node ts t))"
        using list_conc h_split Cons by simp
      then have "ins_list x (inorder (Node ts t)) = inorder (Node ts t)"
        using "2.prems" ins_list_contains_idem by blast
      also have "\<dots> = inorder_up_i (ins k x (Node ts t))"
        using list_split h_split Cons True by auto
      finally show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i a)
        then have IH:"inorder a = ins_list x (inorder sub)"
          using "2.IH"(2) "2.prems" list_split Cons sorted_inorder_sub h_split False
          by auto
        have "inorder_up_i (ins k x (Node ts t)) = inorder_list ls @ inorder a @ sep # inorder_list list @ inorder t"
          using h_split False list_split T_i Cons by simp
        also have "\<dots> = inorder_list ls @ ins_list x (inorder sub) @ sep # inorder_list list @ inorder t"
          using IH by simp
        also have "\<dots> = ins_list x (inorder (Node ts t))"
          using ins_list_split ins_list_split_right
          using list_split "2.prems" Cons h_split False by auto
        finally show ?thesis .
      next
        case (Up_i l a r)
        then have IH:"inorder_up_i (Up_i l a r) = ins_list x (inorder sub)"
          using "2.IH"(2) False h_split list_split local.Cons sorted_inorder_sub
          by auto
        have "inorder_up_i (ins k x (Node ts t)) = inorder_list ls @ inorder l @ a # inorder r  @ sep # inorder_list list @ inorder t"
          using h_split False list_split Up_i Cons by simp
        also have "\<dots> = inorder_list ls @ ins_list x (inorder sub) @ sep # inorder_list list @ inorder t"
          using IH by simp
        also have "\<dots> = ins_list x (inorder (Node ts t))"
          using ins_list_split ins_list_split_right
          using list_split "2.prems" Cons h_split False by auto
        finally show ?thesis .
      qed
    qed
  qed
qed

declare node_i.simps [simp add]
declare node_i_inorder [simp del]


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

lemma tree_i_inorder: "inorder_up_i u = inorder (tree_i u)"
  apply (cases u)
   apply auto
  done

lemma insert_bal: "bal t \<Longrightarrow> bal (insert k x t)"
  using ins_bal
  by (simp add: tree_i_bal)

lemma insert_order: "\<lbrakk>k > 0; root_order k t\<rbrakk> \<Longrightarrow> root_order k (insert k x t)"
  using ins_root_order
  by (simp add: tree_i_order)


lemma insert_inorder: "sorted_less (inorder t) \<Longrightarrow> inorder (insert k x t) = ins_list x (inorder t)"
  using ins_inorder
  by (simp add: tree_i_inorder)

section "Deletion"

thm list.simps

text "The following deletion method is inspired by Bauer (70) and Fielding (??).
Rather than stealing only a single node from the neighbour,
the neighbour is fully merged with the potentially underflowing node.
If the resulting node is still larger than allowed, the merged node is split
again, using the rules known from insertion splits.
If the resulting node has admissable size, it is simply kept in the tree."

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

text "All trees are merged with the right neighbour on underflow.
Obviously for the last tree this would not work since it has no right neighbour.
Therefore this tree, as the only exception, is merged with the left neighbour.
However since we it does not make a difference, we treat the situation
as if the second to last tree underflowed."

fun rebalance_last_tree where
  "rebalance_last_tree k ts t = (
case last ts of (sub,sep) \<Rightarrow>
   rebalance_middle_tree k (butlast ts) sub sep [] t
)"

text "Rather than deleting the minimal key from the right subtree,
we remove the maximal key of the left subtree.
This is due to the fact that the last tree can easily be accessed
and the left neighbour is way easier to access than the right neighbour."



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
        by (metis assms(1) height_up_i.simps(2) height_list_split sub_node t_node)
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
          using Up_i Nil sub_node t_node by auto
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
        by (metis r_node height_up_i.simps(2) height_list_split max.commute sub_node)
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

(* a recursive property of the "spine" we want to walk along for splitting *)
fun nonempty_lasttreebal where
  "nonempty_lasttreebal Leaf = True" |
  "nonempty_lasttreebal (Node ts t) = (
    (\<exists>ls tsub tsep. ts = (ls@[(tsub,tsep)]) \<and> height tsub = height t) \<and>
     nonempty_lasttreebal t
  )"

lemma split_max_height:
  assumes "split_max k t = (sub,sep)"
    and "nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "height sub = height t"
  using assms
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
    case Node2: (Node l a)
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
      using split_fun_req_alt(1) 2 list_split Nil
      by (metis append_Nil2 nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
    moreover have "Node ls t = Node ts t" using split_fun_req_alt(1) Nil list_split by auto
    ultimately show ?thesis
      using rebalance_last_tree_height 2 list_split Nil split_fun_req_alt(1) by auto
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_fun_req_alt(1) by blast
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" | 
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      have "height (del k x sub) = height t"
        using 2 sep_n_x a_split list_split Cons split_fun_set(1)
        by (metis bal.simps(2) order_impl_root_order root_order.simps(2) some_child_sub(1))
      then have "height (rebalance_middle_tree k ls (del k x sub) sep rs t) = height (Node (ls@((del k x sub),sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) \<open>height (del k x sub) = height t\<close> a_split list_split Cons split_fun_set(1) by fastforce
      also have "\<dots> = height (Node ts t)"
        using 2 a_split sep_n_x list_split Cons split_fun_set(1) split_fun_req_alt(1)
        by auto
      finally show ?thesis
        using sep_n_x Cons a_split list_split 2
        by simp
    next
      case sep_x_Leaf
      then have "height (Node ts t) = height (Node (ls@rs) t)"
        using bal_split_last(2) "2.prems"(3) a_split list_split Cons split_fun_req_alt(1)
        by fastforce
      then show ?thesis
        using a_split list_split Cons sep_x_Leaf 2 by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by blast
      obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun_set(1) split_max_height sub_node)
      then have "height (rebalance_middle_tree k ls sub_s max_s rs t) = height (Node (ls@(sub_s,sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node ts t)"
        using 2 a_split sep_x_Node list_split Cons split_fun_set(1) split_fun_req_alt(1) \<open>height sub_s = height t\<close>
        by fastforce
      finally show ?thesis using sep_x_Node Cons a_split list_split 2 sub_node sub_split
        by auto
    qed
  qed
qed simp

(* proof for inorders *)

(* note: this works (as it should, since there is not even recursion involved)
  automatically. *yay* *)
lemma rebalance_middle_tree_inorder:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "inorder (rebalance_middle_tree k ls sub sep rs t) = inorder (Node (ls@(sub,sep)#rs) t)"
  apply(cases sub)
   apply (cases t)
  using assms  apply auto[2]
  apply (cases t)
  using assms node_i_inorder 
   apply (auto
      split!: btree.splits up_i.splits list.splits
      simp del: node_i.simps
      simp add: node_i_inorder_simps
      )
  done

lemma rebalance_last_tree_inorder:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "inorder (rebalance_last_tree k ts t) = inorder (Node ts t)"
  using rebalance_middle_tree_inorder assms by auto

lemma butlast_inorder_app_id: "xs = xs' @ [(sub,sep)] \<Longrightarrow> inorder_list xs' @ inorder sub @ [sep] = inorder_list xs"
  by simp

lemma split_max_inorder:
  assumes "nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "inorder_pair (split_max k t) = inorder t"
  using assms 
proof (induction k t rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then have "ts = butlast ts @ [last ts]"
      using "1.prems"(1) by auto
    moreover obtain sub sep where "last ts = (sub,sep)"
      by fastforce
    ultimately show ?thesis
      using Leaf 
      apply (auto split!: prod.splits btree.splits)
      by (simp add: butlast_inorder_app_id)
  next
    case (Node tts tt)
    then have IH: "inorder_pair (split_max k t) = inorder t"
      using "1.IH" "1.prems"(1) by auto
    obtain sub sep where split_sub_sep: "split_max k t = (sub,sep)"
      by fastforce
    then have height_sub: "height sub = height t"
      by (metis "1.prems"(1) Node btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height)
    have "inorder_pair (split_max k (Node ts t)) = inorder (rebalance_last_tree k ts sub) @ [sep]"
      using Node 1 split_sub_sep by auto
    also have "\<dots> = inorder_list ts @ inorder sub @ [sep]"
      using rebalance_last_tree_inorder height_sub "1.prems"
      by (auto simp del: rebalance_last_tree.simps)
    also have "\<dots> = inorder (Node ts t)"
      using IH split_sub_sep by simp
    finally show ?thesis .
  qed
qed simp


lemma height_bal_subtrees_merge: "\<lbrakk>height (Node as a) = height (Node bs b); bal (Node as a); bal (Node bs b)\<rbrakk>
 \<Longrightarrow> \<forall>x \<in> set (subtrees as) \<union> {a}. height x = height b"
  by (metis Suc_inject Un_iff bal.simps(2) height_bal_tree singletonD)

lemma node_i_bal_alt: 
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
  ultimately show ?thesis using node_i_bal[of "as@(a,x)#bs"]
    by (auto simp del: node_i.simps)
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
        by (metis height_bal_tree height_up_i.simps(2) height_list_split max.idem sub_heights(1) sub_heights(3) sub_node t_node)
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up_i (node_i k (mts@(mt,sep)#tts) tt) = height t" by simp
      moreover have "bal_up_i (node_i k (mts@(mt,sep)#tts) tt)"
        using node_i_bal_alt sub_node t_node sub_heights by auto
      ultimately show ?thesis
        apply (cases "node_i k (mts@(mt,sep)#tts) tt")
        using assms Nil sub_node t_node by auto
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t" "bal rsub"
        using assms Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "height_up_i (node_i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node_i_height by blast
      also have "\<dots> = Suc (height rt)"
        by (metis Un_iff  \<open>height rsub = height t\<close> assms bal.simps(2) bal_split_last(1) height_bal_tree height_up_i.simps(2) height_list_split list.set_intros(1) Cons max.idem r_node r_split set_append some_child_sub(1) sub_heights(1) sub_node)
      also have "\<dots> = height rsub"
        using height_bal_tree r_node rsub_height(2) by fastforce
      finally have 1: "height_up_i (node_i k (mts@(mt,sep)#rts) rt) = height rsub" by simp
      moreover have 2: "bal_up_i (node_i k (mts@(mt,sep)#rts) rt)"
        using node_i_bal_alt sub_node sub_heights rsub_height r_node by auto
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


lemma rebalance_last_tree_bal: "\<lbrakk>bal (Node ts t); ts \<noteq> []\<rbrakk> \<Longrightarrow> bal (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_bal append_butlast_last_id[of ts]
  apply(cases "last ts") 
  apply(auto simp del: bal.simps rebalance_middle_tree.simps)
  done


lemma split_max_bal: 
  assumes "bal t"
    and "t \<noteq> Leaf" 
    and "nonempty_lasttreebal t"
  shows "bal (fst (split_max k t))"
  using assms
proof(induction k t rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then obtain sub sep where last_split: "last ts = (sub,sep)"
      using 1 by auto
    then have "height sub = height t" using 1 by auto
    then have "bal (Node (butlast ts) sub)" using 1 last_split by auto
    then show ?thesis using 1 Leaf last_split by auto
  next
    case (Node tts tt)
    then obtain sub sep where t_split: "split_max k t = (sub,sep)" by (cases "split_max k t")
    then have "height sub = height t" using 1 Node
      by (metis btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height)
    moreover have "bal sub"
      using "1.IH" "1.prems"(1) "1.prems"(3) Node t_split by fastforce
    ultimately have "bal (Node ts sub)"
      using 1 t_split Node by auto
    then show ?thesis
      using rebalance_last_tree_bal t_split Node 1
      by (auto simp del: bal.simps rebalance_middle_tree.simps)
  qed
qed simp

lemma del_bal: 
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
  shows "bal (del k x t)"
  using assms
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls,rs)"
    by (cases "split_fun ts x")
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
      using list_split split_fun_req_alt(1) Nil by fastforce
    then show ?thesis
      using 2 list_split Nil
      by auto
  next
    case (Cons r rs)
    then obtain sub sep where r_split: "r = (sub,sep)" by (cases r)
    then have sub_height: "height sub = height t" "bal sub"
      using 2 Cons list_split split_fun_set(1) by fastforce+
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" | 
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have "bal (del k x sub)" "height (del k x sub) = height sub" using sub_height
        using "2.IH"(2) "2.prems"(2) list_split Cons r_split split_fun_set(1) order_impl_root_order
         apply (metis "2.prems"(1) root_order.simps(2) some_child_sub(1))
        by (metis "2.prems"(1) "2.prems"(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_fun_set(1) sub_height(2))
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split Cons r_split split_fun_req_alt(1) by blast
      ultimately have "bal (Node (ls@(del k x sub,sep)#rs) t)"
        using bal_substitute_subtree[of ls sub sep rs t "del k x sub"] by metis
      then have "bal (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_bal[of ls "del k x sub" sep rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split sep_n_x by auto
    next
      case sep_x_Leaf
      moreover have "bal (Node (ls@rs) t)"
        using bal_split_last(1) list_split split_fun_req_alt(1) r_split
        by (metis "2.prems"(3) Cons)
      ultimately show ?thesis
        using 2 list_split Cons r_split by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height sub"
        using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_height(2) sub_node)
      moreover have "bal sub_s"
        using split_max_bal
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) fst_conv list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_height(2) sub_node sub_split)
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split Cons r_split split_fun_req_alt(1) by blast
      ultimately have "bal (Node (ls@(sub_s,sep)#rs) t)"
        using bal_substitute_subtree[of ls sub sep rs t "sub_s"] by metis
      then have "bal (Node (ls@(sub_s,max_s)#rs) t)"
        using bal_substitute_separator by metis
      then have "bal (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_bal[of ls sub_s max_s rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split sep_x_Node sub_node sub_split by auto
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
        using assms Cons by auto
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
  assumes "order k t"
    and "t \<noteq> Leaf"
    and "nonempty_lasttreebal t"
  shows "almost_order k (fst (split_max k t))"
  using assms
proof(induction k t rule: split_max.induct)
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
      by (metis "1.prems"(3) Node Pair_inject append1_eq_conv btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height sub_split ts_not_empty)
    ultimately have "almost_order k (rebalance_last_tree k ts s_sub)"
      using rebalance_last_tree_order[of ts ls sub sep k s_sub]
        1 ts_not_empty Node sub_split
      by force
    then show ?thesis
      using Node 1 sub_split by auto
  qed
qed simp


lemma subtrees_split2: "set (subtrees (l@r)) = set (subtrees l) \<union> set (subtrees r)"
  apply(induction r)
   apply(auto)
  done

lemma del_order: 
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
  shows "almost_order k (del k x t)"
  using assms
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
      by (metis eq_snd_iff length_greater_0_conv rev_exhaust root_order.simps(2) split_fun_length_l)
    moreover have "height t = height (del k x t)" using del_height 2 by (simp add: order_impl_root_order)
    moreover have "length ls = length ts"
      using Nil list_split split_fun_length_l by auto
    ultimately have "almost_order k (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_order[of ls lls lsub lsep k "del k x t"]
      by (metis "2.prems"(2) "2.prems"(3) Un_iff append_Nil2 bal.simps(2) list_split Nil root_order.simps(2) singletonI split_fun_req_alt(1) subtrees_split)
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
      using Cons "2.prems"(3) bal_sub_height list_split split_fun_req_alt(1) apply (blast)
      using subtrees_split2 2 list_split split_fun_req_alt(1) Cons r_split subtrees_split
        apply (metis Un_iff root_order.simps(2))
      using "2"(4) list_split Cons r_split split_fun_length apply auto
      done

    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" | 
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis 
    proof cases
      case sep_n_x
      then have "almost_order k (del k x sub)" using 2 list_split Cons r_split order_impl_root_order
        by (metis bal.simps(2) root_order.simps(2) some_child_sub(1) split_fun_set(1))
      moreover have "height (del k x sub) = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_fun_set(1))
      ultimately have "almost_order k (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_order[of k "del k x sub" ls rs t sep]
        using inductive_help
        using Cons r_split sep_n_x list_split by auto
      then show ?thesis using 2 Cons r_split sep_n_x list_split by auto
    next
      case sep_x_Leaf
      then have "almost_order k (Node (ls@rs) t)" using inductive_help by auto
      then show ?thesis using 2 Cons r_split sep_x_Leaf list_split by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t" using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_node)
      moreover have "almost_order k sub_s" using split_max_order
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) fst_conv list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1)  sub_node sub_split)
      ultimately have "almost_order k (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_order[of k sub_s ls rs t max_s] inductive_help
        by auto
      then show ?thesis
        using 2 Cons r_split list_split sep_x_Node sub_split by auto
    qed
  qed
qed simp

(* sortedness of delete by inorder *)
(* generalize del_list_sorted since its cumbersome to express inorder_list ts as xs @ [a]
note that the proof scheme is almost identical to ins_list_sorted
 *)
thm del_list_sorted

lemma del_list_split:
  assumes "split_fun ts x = (ls, rs)"
    and "sorted_less (inorder (Node ts t))"
  shows "del_list x (inorder (Node ts t)) = inorder_list ls @ del_list x (inorder_list rs @ inorder t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_fun_req(1))
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  moreover have "sep < x"
  proof -
    have "sep \<in> set (separators ls)"
      by (simp add: ls_tail_split)
    moreover have "sorted_less (separators ts)"
      using assms sorted_inorder_subsepsm sorted_wrt_list_sorted sorted_inorder_impl_list
      by auto
    ultimately show "sep < x"
      using split_fun_req(2) assms(1)
      by blast
  qed
  moreover have "sorted_less (inorder_list ls)"
    using assms sorted_wrt_append split_fun_req_alt(1) by fastforce
  ultimately show ?thesis using assms(2) split_fun_req(1)[OF assms(1)]
    using del_list_sorted[of "inorder_list ls' @ inorder sub" sep]
    by auto
qed

(* del sorted requires sortedness of the full list so we need to change the right specialization a bit *)

lemma del_list_split_right:
  assumes "split_fun ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder (Node ts t))"
    and "sep \<noteq> x"
  shows "del_list x (inorder_list ((sub,sep)#rs) @ inorder t) = del_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
proof -
  from assms have "x < sep"
  proof -
    from assms have "sorted_less (separators ts)"
      using sorted_inorder_subsepsm sorted_wrt_list_sorted by blast
    then show ?thesis
      using split_fun_req(3)
      using assms
      by fastforce
  qed
  moreover have "sorted_less (inorder sub @ sep # inorder_list rs @ inorder t)"
    using assms sorted_wrt_append[where xs="inorder_list ls"] 
    by (auto dest!: split_fun_req(1))
  ultimately show ?thesis
    using del_list_sorted[of "inorder sub" "sep"]
    by auto
qed

thm del_list_idem

lemma del_inorder:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
    and "sorted_less (inorder t)"
  shows "inorder (del k x t) = del_list x (inorder t)"
  using assms
proof (induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs"
    using split_fun.split_fun_req_alt(1) split_fun_axioms by blast
  show ?case
  proof (cases rs)
    case Nil
    then have IH: "inorder (del k x t) = del_list x (inorder t)"
      by (metis "2.IH"(1) "2.prems" bal.simps(2) list_split order_impl_root_order root_order.simps(2) sorted_inorder_last)
    have "inorder (del k x (Node ts t)) = inorder (rebalance_last_tree k ts (del k x t))"
      using list_split Nil list_conc by auto
    also have "\<dots> = inorder_list ts @ inorder (del k x t)"
    proof -
      obtain ts' sub sep where ts_split: "ts = ts' @ [(sub, sep)]"
        by (meson "2.prems"(1) "2.prems"(2) "2.prems"(3) nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
      then have "height sub = height t"
        using "2.prems"(3) by auto
      moreover have "height t = height (del k x t)"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) del_height order_impl_root_order root_order.simps(2))
      ultimately show ?thesis
        using rebalance_last_tree_inorder
        using ts_split by auto
    qed
    also have "\<dots> = inorder_list ts @ del_list x (inorder t)"
      using IH by blast
    also have "\<dots> = del_list x (inorder (Node ts t))"
      using "2.prems"(4) list_conc list_split Nil del_list_split
      by auto
    finally show ?thesis .
  next
    case (Cons h rs)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)
    then have node_sorted_split: 
      "sorted_less (inorder (Node (ls@(sub,sep)#rs) t))"
      "root_order k (Node (ls@(sub,sep)#rs) t)"
      "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems" h_split list_conc Cons by blast+
    consider (sep_n_x) "sep \<noteq> x" | (sep_x_Leaf) "sep = x \<and> sub = Leaf" |  (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have IH: "inorder (del k x sub) = del_list x (inorder sub)"
        by (metis (no_types, lifting) "2.IH"(2) "2.prems"(1) "2.prems"(2) "2.prems"(4) bal.simps(2) h_split list_conc list_split local.Cons node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_inorder_impl_list sorted_inorder_subtrees_induct split_fun_set(1))
      from sep_n_x have "inorder (del k x (Node ts t)) = inorder (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using list_split Cons h_split by auto
      also have "\<dots> = inorder (Node (ls@(del k x sub, sep)#rs) t)"
      proof -
        have "height t = height (del k x sub)"
          using del_height
          using order_impl_root_order "2.prems"
          by (auto simp add: order_impl_root_order Cons list_conc h_split)
        moreover have "case rs of [] \<Rightarrow> True | (rsub, rsep) # list \<Rightarrow> height rsub = height t"
          using "2.prems"(3) bal_sub_height list_conc Cons by blast
        ultimately show ?thesis
          using rebalance_middle_tree_inorder
          by simp
      qed
      also have "\<dots> = inorder_list ls @ del_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
        using IH by simp
      also have "\<dots> = del_list x (inorder (Node ts t))"
        using del_list_split[of ts x ls "(sub,sep)#rs" t]
        using del_list_split_right[of ts x ls sub sep rs t]
        using list_split list_conc h_split Cons "2.prems"(4) sep_n_x
        by auto
      finally show ?thesis .
    next
      case sep_x_Leaf
      then have "del_list x (inorder (Node ts t)) = inorder (Node (ls@rs) t)"
        using list_split list_conc h_split Cons "2.prems"(4)
        using del_list_split[of ts x ls "(sub,sep)#rs" t]
        by simp
      also have "\<dots> = inorder (del k x (Node ts t))"
        using list_split sep_x_Leaf list_conc h_split Cons
        by auto
      finally show ?thesis by simp
    next
      case sep_x_Node
      obtain ssub ssep where split_split: "split_max k sub = (ssub, ssep)"
        by fastforce
      from sep_x_Node have "x = sep"
        by simp
      then have "del_list x (inorder (Node ts t)) = inorder_list ls @ inorder sub @ inorder_list rs @ inorder t"
        using list_split list_conc h_split Cons "2.prems"(4)
        using del_list_split[of ts x ls "(sub,sep)#rs" t]
        apply auto
        using del_list_sorted1[of "inorder sub" sep "inorder_list rs @ inorder t" x]
          sorted_wrt_append
        by auto
      also have "\<dots> = inorder_list ls @ inorder_pair (split_max k sub) @ inorder_list rs @ inorder t"
        using sym[OF split_max_inorder[of sub k]]
        using order_bal_nonempty_lasttreebal[of k sub] "2.prems"
          list_conc h_split Cons sep_x_Node
        by (auto simp del: split_max.simps simp add: order_impl_root_order)
      also have "\<dots> = inorder_list ls @ inorder ssub @ ssep # inorder_list rs @ inorder t"
        using split_split by auto
      also have "\<dots> = inorder (rebalance_middle_tree k ls ssub ssep rs t)"
      proof -
        have "height t = height ssub"
          using split_max_height
          by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) h_split list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) sep_x_Node some_child_sub(1) split_fun.split_fun_set(1) split_fun_axioms split_split)
        moreover have "case rs of [] \<Rightarrow> True | (rsub, rsep) # list \<Rightarrow> height rsub = height t"
          using "2.prems"(3) bal_sub_height list_conc local.Cons by blast
        ultimately show ?thesis
          using rebalance_middle_tree_inorder
          by auto
      qed
      also have "\<dots> = inorder (del k x (Node ts t))"
        using list_split sep_x_Node list_conc h_split Cons split_split
        by auto
      finally show ?thesis by simp
    qed
  qed
qed auto

lemma reduce_root_order: "\<lbrakk>k > 0; almost_order k t\<rbrakk> \<Longrightarrow> root_order k (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits simp add: order_impl_root_order)
  done

lemma reduce_root_bal: "bal (reduce_root t) = bal t"
  apply(cases t)
   apply(auto split!: list.splits)
  done


lemma reduce_root_inorder: "inorder (reduce_root t) = inorder t"
  apply (cases t)
   apply (auto split!: list.splits)
  done


lemma delete_order: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> root_order k (delete k x t)"
  using del_order
  by (simp add: reduce_root_order)

lemma delete_bal: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> bal (delete k x t)"
  using del_bal
  by (simp add: reduce_root_bal)

lemma delete_inorder: "\<lbrakk>k > 0; bal t; root_order k t; sorted_less (inorder t)\<rbrakk> \<Longrightarrow> inorder (delete k x t) = del_list x (inorder t)"
  using del_inorder
  by (simp add: reduce_root_inorder)

(* TODO (opt) runtime wrt runtime of split_fun *)

(* we are interested in a) number of comparisons b) number of fetches c) number of writes *)
(* a) is dependent on t_split_fun, the remainder is not (we assume the number of fetches and writes
for split fun is 0 *)


(* TODO simpler induction schemes /less boilerplate isabelle/src/HOL/ex/Induction_Schema *)

(* Set specification by inorder *)

fun invar_inorder where "invar_inorder k t = (bal t \<and> root_order k t)"

interpretation S_ordered: Set_by_Ordered where
  empty = Leaf and
  insert = "insert (Suc k)" and 
  delete = "delete (Suc k)" and
  isin = "isin"   and
  inorder = "inorder"   and
  inv = "invar_inorder (Suc k)"
proof (standard, goal_cases)
  case (2 s x)
  then show ?case
    by (simp add: isin_set_inorder)
next
  case (3 s x)
  then show ?case using insert_inorder
    by simp
next
  case (4 s x)
  then show ?case using delete_inorder
    by auto
next
  case (6 s x)
  then show ?case using insert_order insert_bal
    by auto
next
  case (7 s x)
  then show ?case using delete_order delete_bal
    by auto
qed simp+


end


text "Finally we show that the split_fun axioms are feasible
       by providing an example split function"

(*TODO: at some point this better be replaced with something binary search like *)
fun linear_split_help:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> _ \<Rightarrow> (_ btree\<times>_) list \<Rightarrow>  ((_ btree\<times>_) list \<times> (_ btree\<times>_) list)" where
  "linear_split_help [] x prev = (prev, [])" |
  "linear_split_help ((sub, sep)#xs) x prev = (if sep < x then linear_split_help xs x (prev @ [(sub, sep)]) else (prev, (sub,sep)#xs))"

fun linear_split:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> _ \<Rightarrow> ((_ btree\<times>_) list \<times> (_ btree\<times>_) list)" where
  "linear_split xs x = linear_split_help xs x []"

(* linear split is similar to well known functions, therefore a quick proof can be done *)

lemma linear_split_alt: "linear_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"
proof -

  have "linear_split_help xs x prev = (prev @ takeWhile (\<lambda>(_, s). s < x) xs, dropWhile (\<lambda>(_, s). s < x) xs)"
    for prev
    apply (induction xs arbitrary: prev)
     apply auto
    done
  thus ?thesis by auto
qed

interpretation btree_linear_search: split_fun linear_split
  apply unfold_locales
  unfolding linear_split_alt
    apply (auto simp: split: list.splits)
  subgoal
    by (meson case_prodD set_takeWhileD)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done


(* however we can also explicitly derive the locale requirements *)

lemma some_child_sm: "linear_split_help t y xs = (ls,(sub,sep)#rs) \<Longrightarrow> y \<le> sep"
  apply(induction t y xs rule: linear_split_help.induct)
   apply(simp_all)
  by (metis Pair_inject le_less_linear list.inject)



lemma linear_split_append: "linear_split_help xs p ys = (ls,rs) \<Longrightarrow> ls@rs = ys@xs"
  apply(induction xs p ys rule: linear_split_help.induct)
   apply(simp_all)
  by (metis Pair_inject)

lemma linear_split_sm: "\<lbrakk>linear_split_help xs p ys = (ls,rs); sorted_less (separators (ys@xs)); \<forall>sep \<in> set (separators ys). p > sep\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (separators ls). p > sep"
  apply(induction xs p ys rule: linear_split_help.induct)
   apply(simp_all)
  by (metis prod.inject)+

value "linear_split [(Leaf, 2)] (1::nat)"

(* TODO still has format for older proof *)
lemma linear_split_gr:
  "\<lbrakk>linear_split_help xs p ys = (ls,rs); sorted_less (separators (ys@xs)); \<forall>(sub,sep) \<in> set ys. p > sep\<rbrakk> \<Longrightarrow> 
(case rs of [] \<Rightarrow> True | (_,sep)#_ \<Rightarrow> p \<le> sep)"
  apply(cases rs)
  by (auto simp add: some_child_sm)


lemma linear_split_req:
  assumes  "linear_split xs p = (ls,rs)"
    and "sorted_less (separators xs)"
  shows "\<forall>sep \<in> set (separators ls). p > sep"
    and "(case rs of [] \<Rightarrow> True | (_,sep)#_ \<Rightarrow> p \<le> sep)"
  using assms linear_split_sm linear_split_gr by fastforce+

definition "linear_insert = insert linear_split"

interpretation btree_linear_search: split_fun linear_split
  by (simp add: linear_split_req linear_split_append split_fun_def)

(* it *is* possible to define a binary split predicate..
however even proving that it terminates is uncomfortable *)

function (sequential) binary_split_help:: "(('a::linorder) btree\<times>'a) list \<Rightarrow> (('a::linorder) btree\<times>'a) list \<Rightarrow> (('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow>  ((_ btree\<times>_) list \<times> (_ btree\<times>_) list)" where
  "binary_split_help ls [] rs x = (ls,rs)" |
  "binary_split_help ls as rs x = (let (mls, mrs) = split_half as in (
  case mrs of (sub,sep)#mrrs \<Rightarrow> (
    if x < sep then binary_split_help ls mls (mrs@rs) x
    else if x > sep then binary_split_help (ls@mls@[(sub,sep)]) mrrs rs x
    else (ls@mls, mrs@rs)
    )
  )
)"
  by pat_completeness auto
termination
  apply(relation "measure (\<lambda>(ls,xs,rs,x). length xs)")
    apply (auto)
  by (metis append_take_drop_id length_Cons length_append lessI trans_less_add2)


fun binary_split where
  "binary_split as x = binary_split_help [] as [] x"


lemma "binary_split_help as bs cs x = (ls,rs) \<Longrightarrow> (as@bs@cs) = (ls@rs)"
  apply(induction as bs cs x arbitrary: ls rs rule: binary_split_help.induct)
   apply (auto simp add: drop_not_empty split!: list.splits )
  subgoal for ls a b va rs  x lsa rsa aa ba x22
    apply(cases "cmp x ba")
      apply auto
      apply (metis Cons_eq_appendI append_eq_appendI append_take_drop_id)
     apply (metis append_take_drop_id)
    by (metis Cons_eq_appendI append_eq_appendI append_take_drop_id)
  done

lemma "\<lbrakk>sorted_less (separators (as@bs@cs)); binary_split_help as bs cs x = (ls,rs); \<forall>y \<in> set (separators as). y < x\<rbrakk>
\<Longrightarrow> \<forall>y \<in> set (separators ls). y < x"
  apply(induction as bs cs x arbitrary: ls rs rule: binary_split_help.induct)
   apply (auto simp add: drop_not_empty split!: list.splits)
  subgoal for ls a b va rs  x lsa rsa aa ba x22 ab bb
    apply(cases "cmp x ba")
      (*apply auto*)
    oops


(* TODO some examples to show that the implementation works and lemmas make sense *)

lemmas [code] = btree_linear_search.insert.simps

value "Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf"
value "root_order 10 (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"
value "bal (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"
thm btree_linear_search.insert.simps

(* BREAKS: no code generated *)
(*value "btree_linear_search.insert 5 10 (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"*)



end