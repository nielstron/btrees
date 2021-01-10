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

lemma split_fun_set_ls: "split_fun ts x = (ls,[]) \<Longrightarrow> set ls = set ts"
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
    using set_map_pred_eq assms
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
    using set_map_pred_eq assms
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

thm le0 length_greater_0_conv

lemma node_i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set ts. order k (fst x)"
    and "order k t"
  shows "order_up_i k (node_i k ts t)"

  apply(cases "node_i k ts t")
  using node_i_root_order node_i_order_helper assms
   apply fastforce
   apply (metis node_i_root_order assms(2,3,4) le0 length_greater_0_conv list.size(3) node_i.simps order_up_i.simps(2) root_order_up_i.simps(2) up_i.distinct(1))
  done



find_theorems "set" "(@)" "(#)"

thm fst_conv


thm node_i_order[of "_" "_@(_,_)#(_,_)#_" "_"]

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

thm bal.simps


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



lemma height_sub_merge: "height t = height s \<Longrightarrow> height (Node (ls@(t,a)#rs) tt) = height (Node (ls@(s,a)#rs) tt)"
  by simp

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

(* ins acts as a Set insertion *)

fun set_up_i where
  "set_up_i (T_i t) = set_btree t" |
  "set_up_i (Up_i l a r) = set_btree l \<union> set_btree r \<union> {a}"

thm BTree.set_btree_induct

lemma up_i_set: "set_btree (Node (ls@(sub,sep)#rs) t) = set_up_i (Up_i (Node ls sub) sep (Node rs t))"
  by auto

lemma node_i_set: "set_up_i (node_i k ts t) = set_btree (Node ts t)"
proof (cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where split_half_ts: 
    "take (length ts div 2) ts = ls"
    "drop (length ts div 2) ts = (sub,sep)#rs" 
    using split_half_not_empty[of ts]
    by auto
  then have "set_btree (Node ts t) = set_up_i (Up_i (Node ls sub) sep (Node rs t))"
    using up_i_set
    by (metis append_take_drop_id)
  also have "\<dots> = set_up_i (node_i k ts t)"
    using False split_half_ts
    by simp
  finally show ?thesis
    by simp
qed simp

find_theorems set_btree
thm btree.set


lemma ins_set: "set_up_i (ins k x t) = set_btree t \<union> {x}"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split_fun ts x = (ls, rs)"
    by (cases "split_fun ts x")
  then have split_app: "ls@rs = ts"
    using split_fun_req_alt(1)
    by auto

  show ?case
  proof (cases rs)
    case Nil
    then have ins_set: "set_up_i (ins k x t) = set_btree t \<union> {x}"
      using 2 split_res by simp
    then show ?thesis 
    proof (cases "ins k x t")
      case (T_i a)
      then show ?thesis
        using ins_set local.Nil split_app split_res
        by auto
    next
      case (Up_i l a r)
      then have "set_up_i (node_i k (ls@[(l,a)]) r) = set_btree (Node (ls@[(l,a)]) r)"
        using node_i_set
        by (simp del: node_i.simps)
      also have "\<dots> = set_btree (Node ts t) \<union> {x}"
        using 2 split_app Nil ins_set Up_i
        by auto
      finally show ?thesis
        by (simp add: Up_i Nil split_res)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then show ?thesis
    proof (cases "sep = x")
      case False
      then have ins_set: "set_up_i (ins k x sub) = set_btree sub \<union> {x}"
        using 2 split_res Cons
        by (simp add: a_split)
      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i a)
        then have "set_btree (Node (ls @ (a,sep) # list) t) = set_btree (Node (ls @ (sub,sep) # list) t) \<union> {x}"
          using ins_set set_btree_split
          by auto
        also have "\<dots> = set_btree (Node ts t) \<union> {x}"
          using split_app Cons a_split
          by simp
        finally show ?thesis
          using 2 Cons a_split split_res T_i False
          by simp
      next
        case (Up_i l a r)
        then have "set_up_i (node_i k (ls @ (l,a)#(r,sep)#list) t) = set_btree (Node (ls @ (l,a)#(r,sep)#list) t)"
          using node_i_set
          by (simp del: node_i.simps)
        also have "\<dots> = set_btree (Node (ls@(sub,sep)#list) t) \<union> {x}"
          using ins_set Up_i set_btree_split
          by auto
        also have "\<dots> = set_btree (Node ts t) \<union> {x}"
          using split_app Cons a_split
          by simp
        finally show ?thesis 
          using Up_i a_split Cons split_app split_res False
          by simp
      qed
    next
      case True
      then have "x \<in> set_btree (Node ts t)"
        by (metis a_split local.Cons set_btree_induct some_child_sub(2) split_fun_set(1) split_res)
      then have "set_btree (Node ts t) = set_btree (Node ts t) \<union> {x}"
        by blast
      then show ?thesis
        using a_split 2 Cons True split_res
        by simp
    qed
  qed
qed simp


(* sorted_less invariant *)

thm sorted_btree.simps

find_theorems sorted_wrt take

fun sorted_up_i where
  "sorted_up_i (T_i t) = sorted_btree t" |
  "sorted_up_i (Up_i l a r) = (sorted_btree l \<and> sorted_btree r \<and> sub_sep_cons (l,a) \<and> (\<forall>y \<in> set_btree r. a < y))"


lemma sorted_btree_split_rs: "sorted_btree (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_btree (Node rs t) \<and>  (\<forall>r \<in> set (separators rs). sep < r)"
  apply(induction ls)
   apply(auto)
  done

lemma sorted_btree_split_ls: "sorted_btree (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> sorted_btree (Node ls sub) \<and>  (\<forall>l \<in> set (separators ls). l < sep)"
  apply(induction ls)
   apply(auto)
  done

lemma up_i_sorted:
  assumes "sorted_btree (Node (ls@(sub,(sep::('a::linorder)))#rs) t)"
  shows "sorted_up_i (Up_i (Node ls sub) sep (Node rs t))"
  unfolding sorted_up_i.simps
proof (safe)
  have "sorted_wrt sub_sep_sm ((sub,sep)#rs)"
    using assms sorted_btree.simps(2) sorted_wrt_append by blast
  then have
    "\<forall>r \<in> set (subtrees rs). \<forall>x \<in> set_btree r. sep < x"
    "\<forall>r \<in> set (separators rs). sep < r"
    by (auto simp add: sorted_wrt_sorted_left)
  moreover have "\<forall>r \<in> set_btree t. sep < r"
    using assms by auto
  ultimately show "\<And>x. x \<in> set_btree (Node rs t) \<Longrightarrow> sep < x"
    using set_btree_induct by auto
next
  show "sorted_btree (Node rs t)" "sorted_btree (Node ls sub)"
    using sorted_btree_split_rs sorted_btree_split_ls assms append_take_drop_id
    by metis+
next
  show "sub_sep_cons (Node ls sub, sep)"
    unfolding sub_sep_cons.simps
    using sorted_wrt_sorted_right2[of ls sub sep rs] assms
    by simp
qed


lemma node_i_sorted:
  assumes "sorted_btree (Node ts t)"
  shows "sorted_up_i (node_i k ts t)"
  using assms
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where split_half_ts: 
    "take (length ts div 2) ts = ls"
    "drop (length ts div 2) ts = (sub,sep)#rs" 
    using split_half_not_empty[of ts]
    by auto
  then have "sorted_up_i (Up_i (Node ls sub) sep (Node rs t))"
    using up_i_sorted assms
    by (metis append_take_drop_id)
  then show ?thesis
    using False split_half_ts
    by simp
qed simp

thm btree.set
thm sorted_wrt_append

(* Example extracted proof 1 *)
lemma sorted_up_i_append:
  assumes "sorted_up_i (Up_i l a r)"
    and "\<forall>x \<in> set (separators ls). \<forall>y \<in> set_up_i (Up_i l (a::(_::linorder)) r). x < y"
    and "sorted_btree (Node ls t)"
  shows "sorted_btree (Node (ls@[(l,a)]) r)"
  unfolding sorted_btree.simps
proof(safe)
  show "sorted_wrt sub_sep_sm (ls @ [(l, a)])"
    unfolding sorted_wrt_split
  proof (safe)
    fix sub sep assume "(sub,sep) \<in> set ls"
    then have "sep \<in> set (separators ls)"
      by (meson some_child_sub(2))
    then have "sep < a" "\<forall>x \<in> set_btree l. sep < x"
      by (simp_all add: assms)
    then show "sub_sep_sm (sub,sep) (l,a)"
      by simp
  next
    show "sorted_wrt sub_sep_sm ls"
      using assms by simp
  qed simp_all
next
  show "sorted_btree r"
    using assms
    by auto
next
  fix z y assume "z \<in> set (separators (ls@[(l,a)]))" "y \<in> set_btree r"
  then have "z \<in> set (separators ls) \<or> z = a"
    by auto
  then show "z < y"
  proof
    assume "z \<in> set (separators ls)"
    then show "z < y"
      by (simp add: \<open>y \<in> set_btree r\<close> assms(2))
  next
    assume "z = a"
    then show "z < y"
      using \<open>y \<in> set_btree r\<close> assms(1) sorted_up_i.simps(2) by blast 
  qed
next
  show
    "\<And>aa b. (aa, b) \<in> set (ls @ [(l, a)]) \<Longrightarrow> sub_sep_cons (aa, b)"
    "\<And>x. x \<in> set (subtrees (ls @ [(l, a)])) \<Longrightarrow> sorted_btree x "
    using assms
    by auto
qed

(* Example extracted proof 2 *)
lemma sorted_sub_merge:
  assumes "sorted_btree sub"
    and "\<forall>x \<in> set (separators ls). \<forall>y \<in> set_btree sub. x < y"
    and "\<forall>x \<in> set (separators rs). \<forall>y \<in> set_btree sub. x > y"
    and "\<forall>y \<in> set_btree sub. sep > y"
    and "sorted_btree (Node (ls@(m,(sep::(_::linorder)))#rs) t)"
  shows "sorted_btree (Node (ls@(sub,sep)#rs) t)"
  unfolding sorted_btree.simps
proof (safe)
  show "sorted_wrt sub_sep_sm (ls@(sub,sep)#rs)"
    unfolding sorted_wrt_split
  proof (safe)      
    fix lsub lsep assume "(lsub,lsep) \<in> set ls"
    then show "sub_sep_sm (lsub,lsep) (sub,sep)"
      unfolding sub_sep_sm.simps
      by (meson assms(2) assms(5) some_child_sub(2) sorted_btree_split_ls)
  next show "sorted_wrt sub_sep_sm ls" "sorted_wrt sub_sep_sm rs" using assms
      by (simp add: sorted_wrt_split)+
  next 
    fix a b assume "(a,b) \<in> set rs"
    then show "sub_sep_sm (sub, sep) (a, b) "
      unfolding sub_sep_sm.simps
      by (meson assms(5) some_child_sub(1) some_child_sub(2) sorted_btree_sorted sorted_btree_split_rs sorted_inorder_subsepsm sorted_wrt_append sorted_wrt_sorted_left)
  qed
next
  fix a b assume "(a, b) \<in> set (ls @ (sub, sep) # rs)"
  then show "sub_sep_cons (a, b)"
    by (metis Un_iff assms(4) assms(5) list.set_intros(2) set_ConsD set_append sorted_btree.simps(2) sub_sep_cons.simps)
next
  fix s x assume "s \<in> set (separators (ls@(sub,sep)#rs))" "x \<in> set_btree t"
  then show "s < x"
    by (metis assms(5) separators_split sorted_btree.simps(2))
next
  fix s assume "s \<in> set (subtrees (ls @ (sub, sep) # rs))"
  then show "sorted_btree s"
    by (metis Un_iff assms(1) assms(5) singletonD sorted_btree.simps(2) subtrees_split)
next
  show "sorted_btree t" using assms(5) by simp
qed


(* sorted_less of ins *)
lemma ins_sorted: "sorted_btree t \<Longrightarrow> sorted_up_i (ins k (x::('a::linorder)) t)"
proof (induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split_fun ts x = (ls,rs)"
    by (cases "split_fun ts x")
  then show ?case
  proof (cases rs)
    case Nil
    then have ls_sorted: "sorted_btree (Node ls t)" 
      using list_split 2 split_fun_req_alt(1)
      by fastforce
    moreover have ins_sorted: "sorted_up_i (ins k x t)"
      using 2 Nil list_split
      by simp
    moreover have ins_set: "\<forall>y \<in> set_up_i (ins k x t). \<forall> sep \<in> set (separators ls). sep < y"
    proof -
      have "set_up_i (ins k x t) = set_btree t \<union> {x}"
        by (simp add: ins_set)
      then show ?thesis
        using list_split Nil ls_sorted sorted_wrt_list_sorted split_fun.split_fun_req_alt(1) split_fun.split_fun_req_alt(2) split_fun_axioms
        by fastforce
    qed
    show ?thesis
    proof (cases "ins k x t")
      case (T_i a)
      then have "sorted_btree a"
        using ins_sorted by simp
      moreover have "\<forall>y \<in> set_btree a. \<forall> sep \<in> set (separators ls). sep < y"
        using ins_set T_i by auto
      ultimately show ?thesis
        using ls_sorted
        by (simp add: T_i list_split Nil)
    next
      case (Up_i l a r)
      then have "\<forall>x \<in> set (separators ls). \<forall>y \<in> set_up_i (Up_i l a r). x < y"
        using ins_set Up_i by auto
      then have "sorted_btree (Node (ls@[(l,a)]) r)"
        using sorted_up_i_append
        by (metis Up_i ins_sorted ls_sorted)
      then show ?thesis
        using 2 Up_i list_split Nil  node_i_sorted[of "ls@[(l,a)]" r]
        by (simp del: node_i.simps)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    have sub_lists_sorted:
      "sorted_wrt sub_sep_sm (ls@(sub,sep)#[])"
      "sorted_wrt sub_sep_sm ((sub,sep)#list)"
       apply (metis (mono_tags, lifting) "2.prems" a_split list_split Cons sorted_btree.simps(2) sorted_wrt_Cons sorted_wrt_split split_fun_req_alt(1) sorted_wrt1)
      apply (metis (mono_tags, lifting) "2.prems" list_split a_split Cons sorted_btree.simps(2) sorted_wrt_Cons sorted_wrt_split split_fun_req_alt(1))
      done
    have ts_split: "ts = ls@(sub,sep)#list"
      using split_fun_req_alt(1) list_split Cons a_split
      by auto
    then have sub_list:
      "\<forall>x \<in> set (ls@(sub,sep)#list). sub_sep_cons x"
      "\<forall>x \<in> set (subtrees (ls@(sub,sep)#list)). sorted_btree x"
      using "2.prems" sorted_btree.simps(2)
      by blast+
    then show ?thesis
    proof (cases "sep = x")
      case True
      then show ?thesis using 2 Cons True list_split a_split
        by simp
    next
      case False
      have sub_sorted: "sorted_up_i (ins k x sub)"
        using 2 a_split list_split Cons False split_fun_set(1)
        by fastforce
      have sub_set: "set_up_i (ins k x sub) = set_btree sub \<union> {x}"
        by (simp add: ins_set)

      then show ?thesis
      proof (cases "ins k x sub")
        case (T_i a)
        then have "sorted_btree a"
          using sub_sorted by auto
        moreover have "\<forall>x \<in> set (separators ls). \<forall>y \<in> set_btree a. x < y"
          using sub_set
          by (metis (mono_tags, lifting) "2.prems" T_i Un_iff ball_empty insertE list_split set_up_i.simps(1) sorted_btree.simps(2) sorted_btree_split_ls sorted_wrt_list_sorted split_fun.split_fun_req_alt(2) split_fun_axioms ts_split)
        moreover have "\<forall>x \<in> set (separators list). \<forall>y \<in> set_btree a. x > y"
          using sorted_wrt_sorted_left2
          by (metis (no_types, lifting) "2.prems" T_i Un_iff a_split ball_empty case_prodD dual_order.strict_trans insertE less_irrefl list.simps(5) list_split local.Cons set_up_i.simps(1) sorted_btree.simps(2) sorted_wrt_list_sorted split_fun.split_fun_req_alt(3) split_fun_axioms split_fun_set(1) sub_lists_sorted(2) sub_sep_cons.simps sub_set)
        moreover have "sub_sep_cons (a,sep)"
          unfolding sub_sep_cons.simps
        proof
          fix y assume "y \<in> set_btree a"
          then have "y \<in> set_btree sub \<or> y = x"
            using T_i sub_set by auto
          then show "y < sep"
          proof
            have "sub_sep_cons (sub,sep)"
              using a_split list_split local.Cons split_fun_set(1) sub_list(1) ts_split
              by blast
            then show "y \<in> set_btree sub \<Longrightarrow> y < sep"
              by auto
          next
            have "x < sep" (* TODO make lemma *)
              using split_fun_req_alt ts_split list_split False
              by (metis (no_types, lifting) "2.prems" a_split case_prod_unfold list.simps(5) local.Cons order.not_eq_order_implies_strict snd_conv sorted_btree.simps(2) sorted_wrt_list_sorted)
            then show "y = x \<Longrightarrow> y < sep"
              by simp
          qed
        qed
        ultimately have "sorted_btree (Node (ls@(a,sep)#list) t)"
          using sorted_sub_merge
          by (metis (no_types, lifting) "2.prems" sub_sep_cons.simps ts_split)
        then show ?thesis
          using 2 a_split list_split Cons False T_i
          by simp
      next
        case (Up_i l a r)
        have "sorted_btree (Node (ls@(l,a)#(r,sep)#list) t)"
          unfolding sorted_btree.simps
        proof (safe)
          fix suba sepa assume a_in_set: "(suba, sepa) \<in> set (ls @ (l, a) # (r, sep) # list)"
          have "set_btree r \<subseteq> set_btree sub \<union> {x}"
            using Up_i sub_set by auto
          moreover have "x < sep"
            using False "2.prems" a_split list_split Cons sorted_wrt_list_sorted split_fun_req_alt(3)
            by fastforce
          ultimately have "sub_sep_cons (r, sep)"
            using sub_list
            by fastforce
          moreover have "sub_sep_cons (l,a)"
            using sub_sorted Up_i by simp
          ultimately show "sub_sep_cons (suba, sepa)"
            using a_in_set sub_list
            by force
        next
          fix y assume "y \<in> set (subtrees (ls@(l,a)#(r,sep)#list))"
          then show "sorted_btree y"
            using sub_list sub_sorted Up_i
            by auto
        next
          show "sorted_btree t"
            using 2 by simp
        next
          fix ty z assume assms:  "ty \<in> set_btree t" "z \<in> set (separators (ls @ (l, a) # (r, sep) # list))"
          then have "(z \<in> set (separators ls) \<union> set (separators list) \<union> {sep}) \<or> z = a"
            using separators_split by auto
          then show "z < ty"
          proof
            have "\<forall>y \<in> set_btree sub. y < ty" "x < ty"
              using "2.prems" a_split assms(1) list_split Cons split_fun_set(1) sorted_wrt_list_sorted split_fun_req_alt(3)
              by fastforce+
            moreover have "a \<in> set_btree sub \<union> {x}" using sub_set Up_i
              by auto
            ultimately have "a < ty" by blast
            moreover assume "z = a"
            ultimately show "z < ty" by simp
          next
            assume "z \<in> set (separators ls) \<union> set (separators list) \<union> {sep}"
            then show "z < ty"
              by (metis "2.prems" a_split assms(1) list_split Cons separators_split sorted_btree.simps(2) split_fun_req_alt(1))
          qed
        next
          have "sub_sep_sm (l,a) (r,sep)"
          proof -
            have "\<forall>x \<in> set_btree r. a < x"
              using Up_i sub_sorted
              by auto
            moreover have "a < sep"
              by (metis (no_types, lifting) False "2.prems" Un_insert_right Up_i a_split case_prod_unfold insert_iff less_le list.simps(5) list_split Cons set_up_i.simps(2) snd_conv sorted_btree.simps(2) sorted_wrt_list_sorted split_fun_req_alt(3) split_fun_set(1) sub_sep_cons.simps sub_set sup_bot.right_neutral)
            ultimately show ?thesis by simp
          qed
          moreover have "\<forall>y \<in> set ls. sub_sep_sm y (l,a)"
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
                using \<open>\<forall>y\<in>set ls. sub_sep_sm y (sub, sep)\<close> y_in_ls
                by auto
              moreover have "ysep < x"
                using "2.prems" y_split y_in_ls list_split sorted_wrt_list_sorted split_fun_req_alt(2)
                by fastforce
              ultimately have "\<forall>z \<in> set_btree l. ysep < z" "ysep < a"
                using Up_i sub_set by auto
              then show "sub_sep_sm y (l, a)"
                by (simp add: y_split)
            qed
          qed
          moreover have "\<forall>y \<in> set list. sub_sep_sm (r,sep) y"
            using sorted_r_forall sub_lists_sorted(2)
            by auto
          ultimately show "sorted_wrt sub_sep_sm (ls @ (l, a) # (r, sep) # list)"
            unfolding sorted_wrt_split2
            using sorted_wrt_append sub_lists_sorted(1) sub_lists_sorted(2)
            by fastforce
        qed
        then show ?thesis using 2 a_split list_split Cons False Up_i
          by (simp del: node_i.simps add: node_i_sorted)
      qed
    qed
  qed
qed simp

fun inorder_up_i where
  "inorder_up_i (T_i t) = inorder t" |
  "inorder_up_i (Up_i l a r) = inorder l @ [a] @ inorder r"


lemma node_i_inorder: "inorder_up_i (node_i k ts t) = inorder (Node ts t)"
  apply(cases "length ts \<le> 2*k")
   apply (auto split!: list.splits)
(* we want to only transform in one direction here.. *)
   supply R = sym[OF append_take_drop_id, of "map _ ts" "(length ts div 2)"]
  thm R
  apply(subst R)
  apply (simp del: append_take_drop_id add: take_map drop_map)
  done


lemma ins_sorted_inorder: "sorted_less (inorder t) \<Longrightarrow> (inorder_up_i (ins k (x::('a::linorder)) t)) = ins_list x (inorder t)"
  apply(induction k x t rule: ins.induct)
  using split_fun_axioms apply (auto split!: prod.splits list.splits up_i.splits simp del: node_i.simps
simp add: node_i_inorder)
  thm split_fun_drule
     apply(drule split_fun_req(1), simp) (* no! *)
(* from here on we need an explicit proof, showing that
   we can apply ins_list_snoc/ins_list_sorted  *)
  oops

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


lemma tree_i_sorted: "sorted_up_i u \<Longrightarrow> sorted_btree (tree_i u)"
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

lemma insert_sorted: "sorted_btree t \<Longrightarrow> sorted_btree (insert k x t)"
  using ins_sorted
  by (simp add: tree_i_sorted)

lemma insert_set: "set_btree t \<union> {x} = set_btree (insert k x t)"
  using ins_set
  by (simp add: tree_i_set)


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
        by (cases "node_i k (mts@(mt,sep)#tts) tt")
          (auto simp add: t_node sub_node set_btree_split False Nil)
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
    case Node2: (Node l a)
    then obtain subsub subsep where sub_split: "split_max k t = (subsub,subsep)" by (cases "split_max k t")
    then have "set_btree subsub \<union> {subsep} = set_btree t" using Node1 Node2 by auto
    moreover have "height subsub = height t"
      by (metis Node1.prems(2) Node2 btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height sub_split)
    ultimately have "set_btree (rebalance_last_tree k ts subsub) \<union> {subsep} = set_btree (Node ts t)"
      using rebalance_last_tree_set Node1 Node2
      by (metis (no_types, lifting) Un_insert_right nonempty_lasttreebal.simps(2) set_btree_split(2) sup_bot.right_neutral)
    moreover have "split_max k (Node ts t) = (rebalance_last_tree k ts subsub, subsep)"
      using Node1 Node2 ts_split sub_split
      by auto
    ultimately show ?thesis using rebalance_last_tree_set Node1 Node2
      by auto
  qed
qed auto

lemma sorted_left_right:
  assumes "sorted_wrt sub_sep_sm ts"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "split_fun ts x = (ls,rs)"
    and "\<forall>sep \<in> set (separators ts). \<forall>y \<in> set_btree t. sep < y"
  shows "\<forall>y \<in> set_btree_list ls. y < x"
    and "case rs of [] \<Rightarrow> True | a#rs \<Rightarrow> (\<forall>y \<in> set_btree_list rs. y > x) \<and> (\<forall>y \<in> set_btree t. y > x)"
proof -
  show "\<forall>y\<in>set_btree_list ls. y < x"
  proof
    fix y assume "y \<in> set_btree_list ls"
    then obtain a where a_set: "a \<in> set ls \<and> y \<in> set_btree_pair a"
      by auto
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have sep_sm: "sep < x"
      using a_split a_set assms(1) assms(3) sorted_wrt_list_sorted split_fun_req_alt(2)
      by fastforce
    then show "y < x"
      using a_set a_split assms(2) assms(3) sep_sm sorted_wrt_sorted_right split_fun_req_alt(1)
      by fastforce
  qed
next
  show "case rs of [] \<Rightarrow> True | a#rs \<Rightarrow> (\<forall>y \<in> set_btree_list rs. y > x) \<and> (\<forall>y \<in> set_btree t. y > x)"
  proof (cases rs)
    case (Cons b rs)
    then obtain sub sep where b_split: "b = (sub,sep)"
      by (cases b)
    then have "sep \<ge> x"
      using assms(1) assms(3) Cons sorted_wrt_list_sorted split_fun_req_alt(3)
      by fastforce
    moreover have "\<forall>y \<in> set_btree_list rs. y > sep" 
    proof 
      fix y assume "y \<in> set_btree_list rs"
      then obtain a where a_set: "a \<in> set rs \<and> y \<in> set_btree_pair a" 
        by auto
      then obtain asub asep where a_split: "a = (asub,asep)"
        by (cases a)
      then have "y \<in> set_btree asub \<or> y = asep"
        using assms a_set
        by auto
      then show "y > sep"
      proof
        assume "y \<in> set_btree asub"
        then show "sep < y"
          by (metis b_split a_set a_split assms(1) assms(3) Cons some_child_sub(1) sorted_wrt_append sorted_wrt_sorted_left split_fun_req_alt(1))
      next
        assume "y = asep"
        then show "sep < y"
          by (metis b_split a_set a_split assms(1) assms(3) Cons sorted_r_forall sorted_wrt_append split_fun_req_alt(1) sub_sep_sm.simps)
      qed
    qed
    moreover have "\<forall>y \<in> set_btree t. y > sep"
      using b_split assms(3) assms(4) Cons split_fun_set(1)
      by fastforce
    ultimately show ?thesis
      using Cons by fastforce
  qed simp
qed

lemma sorted_split_contains:
  assumes "sorted_wrt sub_sep_sm ts"
    and "\<forall>x \<in> set ts. sub_sep_cons x"
    and "(\<forall>sep \<in> set (separators ts). \<forall>y \<in> set_btree t. sep < y)"
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

lemma del_set: "\<lbrakk>k > 0; root_order k t; bal t; sorted_btree t\<rbrakk> \<Longrightarrow> set_btree (del k x t) = set_btree t - {x}"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split_fun ts x = (ls, list)" by (cases "split_fun ts x")
  then have "\<forall>sep \<in> set (separators ls). sep < x"
    by (meson "2.prems"(4) list_split sorted_btree.simps(2) sorted_wrt_list_sorted split_fun_req_alt(2))
  then show ?case
  proof(cases list)
    case Nil
    then obtain lls sub sep where ls_last: "ls = lls@[(sub,sep)]"
      using split_fun_req_alt(1) 2
      by (metis append_Nil2 list_split nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)

    have "set_btree (del k x t) = set_btree t - {x}"
      using 2 Nil list_split
      by (simp add: order_impl_root_order)
    moreover have "x \<notin> set_btree_list ls" using sorted_split_contains
        "2.prems"(4) list_split sorted_btree.simps(2) by blast
    ultimately have "set_btree (Node ls t) - {x} = set_btree (Node ls (del k x t))"
      by auto
    also have "\<dots> = set_btree (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_set 2 list_split Nil del_height ls_last
      by (metis append_Nil2 bal.simps(2) nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) split_fun_req_alt(1))
    finally show ?thesis unfolding del.simps using Nil 2 list_split
      by (metis (no_types, lifting) append_Nil2 case_prod_conv list.simps(4) split_fun_req_alt(1))
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_fun_req_alt(1) by blast
    from Cons list_split have x_not_sub: "x \<notin> set_btree_list rs" "x \<notin> set_btree_list ls" "x \<notin> set_btree t"
      using sorted_split_contains 2
      by (metis list.simps(5) sorted_btree.simps(2))+
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" | 
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      have sub_height: "height (del k x sub) = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) list_split Cons order_impl_root_order root_order.simps(2) some_child_sub(1) del_height split_fun_set(1))
      from sep_n_x have sub_set: "set_btree (del k x sub) = set_btree sub - {x}"
        by (metis "2.IH"(2) "2.prems" a_split bal.simps(2) list_split Cons order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_btree.simps(2) split_fun_set(1))
      have "set_btree (rebalance_middle_tree k ls (del k x sub) sep rs t) = 
            set_btree (Node (ls@(del k x sub,sep)#rs) t)"
        using rebalance_middle_tree_set rs_height sub_height by simp
      also have "\<dots> = set_btree_list ls \<union> set_btree (del k x sub) \<union> {sep} \<union> set_btree_list rs \<union> set_btree t"
        using set_btree_split by auto
      also have "\<dots> = (set_btree_list ls \<union> set_btree sub \<union> {sep} \<union> set_btree_list rs \<union> set_btree t) - {x}"
        using sorted_split_contains sep_n_x x_not_sub sub_set by blast
      also have "\<dots> = set_btree (Node (ls@(sub,sep)#rs) t) - {x}"
        by auto
      finally show ?thesis unfolding del.simps
        using a_split sep_n_x list_split Cons split_fun_req_alt(1)
        by force
    next
      case sep_x_Leaf
      then have "set_btree (Node (ls@rs) t) = set_btree_list ls \<union> set_btree_list rs \<union> set_btree t"
        using set_btree_split by simp
      also have "\<dots> = (set_btree_list ls \<union> set_btree_list rs \<union> set_btree t) - {x}"
        using x_not_sub by simp
      also have "\<dots> = (set_btree_list ls \<union> {x} \<union> {} \<union> set_btree_list rs \<union> set_btree t) - {x}"
        by simp
      also have "\<dots> = set_btree (Node (ls@(Leaf,x)#rs) t) - {x}"
        using set_btree_split by simp
      finally show ?thesis unfolding del.simps
        using a_split sep_x_Leaf list_split Cons split_fun_req_alt(1)
        by force
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      from sep_x_Node 2 have "x \<notin> set_btree sub"
        by (metis a_split list_split Cons not_less_iff_gr_or_eq sorted_btree.simps(2) split_fun_set(1) sub_sep_cons.simps)
      obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have set_sub: "set_btree sub = set_btree sub_s \<union> {max_s}"
        using split_max_set
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_node)

      from sub_split have "height sub_s = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_fun_set(1) split_max_height sub_node)
      then have "set_btree (rebalance_middle_tree k ls sub_s max_s rs t) =
                 (set_btree (Node (ls@(sub_s,max_s)#rs) t))"
        using rebalance_middle_tree_set
        by (metis "2.prems"(3) bal_sub_height list_split Cons split_fun_req_alt(1))
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
        using sep_x_Node Cons a_split list_split split_fun_req_alt(1) by auto
      finally show ?thesis unfolding del.simps
        using sep_x_Node Cons a_split list_split sub_node sub_split by auto
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
        by (metis height_bal_tree height_up_i.simps(2) height_list_split max.idem sub_heights(1) sub_heights(3) sub_node t_node)
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up_i (node_i k (mts@(mt,sep)#tts) tt) = height t" by simp
      moreover have "bal_up_i (node_i k (mts@(mt,sep)#tts) tt)"
        using height_bal_node_i sub_node t_node sub_heights by auto
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
        by (metis Un_iff  \<open>height rsub = height t\<close> assms bal.simps(2) bal_split_last height_bal_tree height_up_i.simps(2) height_list_split list.set_intros(1) Cons max.idem r_node r_split set_append some_child_sub(1) sub_heights(1) sub_node)
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
        using bal_split_last list_split split_fun_req_alt(1) r_split
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
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) sub_height(2) sub_node sub_split)
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

thm prod.split

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
      by (metis eq_snd_iff length_greater_0_conv rev_exhaust root_order.simps(2) split_fun_length_l split_fun_axioms)
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
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_fun_axioms split_fun_set(1))
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
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_fun_set(1) split_fun_axioms sub_node sub_split)
      ultimately have "almost_order k (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_order[of k sub_s ls rs t max_s] inductive_help
        by auto
      then show ?thesis
        using 2 Cons r_split list_split sep_x_Node sub_split by auto
    qed
  qed
qed simp

(* TODO sortedness of delete *)

find_theorems sorted_btree
find_theorems sorted_wrt sub_sep_sm
find_theorems set separators

lemma subtree_in_subtrees: "a \<in> set (subtrees (ls @ (a, b) # rs))"
  by simp

lemma subtree_sub_sm:
  assumes "\<forall>x \<in> set_btree (Node tts tt). a < x"
    and "(c,d) \<in> set tts"
  shows "a < d"
    and "\<forall>y \<in> set_btree c. a < y"
  using assms apply (meson separators_in_set some_child_sub(2) subsetD)
  using assms apply fastforce
  done

lemma sorted_sub_sep_impl: "sorted_btree (Node (ls @ (sub, sep) # rs) t) \<Longrightarrow> \<forall>y \<in> set_btree t. sep < y"
  by simp

lemma rebalance_middle_tree_sorted:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "sorted_btree (Node (ls@(sub,sep)#rs) t)"
  shows "sorted_btree (rebalance_middle_tree k ls sub sep rs t)"
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
    "sorted_wrt sub_sep_sm (ls@[(sub,sep)])"
    "sorted_wrt sub_sep_sm ls" 
    "sorted_wrt sub_sep_sm ((sub,sep)#rs)"
    "\<forall>x \<in> set ls. sub_sep_cons x"
    "\<forall>x \<in> set rs. sub_sep_cons x"
    "sub_sep_cons (sub,sep)"
    using assms(3) sorted_wrt_split
    unfolding sorted_btree.simps
    unfolding sorted_wrt_split
    by auto
  then show ?thesis
    using assms t_node sub_node proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "sorted_btree (Node (mts@(mt,sep)#tts) tt)" unfolding sorted_btree.simps
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
            by (metis (no_types) Un_iff assms(3) list.set_intros(1) separators_in_set set_append some_child_sub(2) sorted_btree.simps(2) sub_node sub_sep_cons.simps sub_sep_sm.simps subsetD)
        next
          fix a b assume "(a, b) \<in> set tts"
          then have "sep < b" "\<forall>y \<in> set_btree a. sep < y"
            using subtree_sub_sm assms t_node sorted_sub_sep_impl
            by metis+
          then show "sub_sep_sm (mt, sep) (a, b)"
            by simp
        qed
      next
        fix a b assume "(a, b) \<in> set (mts @ (mt, sep) # tts)"
        show "sub_sep_cons (a,b)"
          by (metis (no_types, lifting) Un_iff \<open>(a, b) \<in> set (mts @ (mt, sep) # tts)\<close> assms(3) insert_iff list.set(2) set_append set_btree_split(2) sorted_btree.simps(2) sub_node sub_sep_cons.simps subtree_in_subtrees t_node)
      next
        fix x assume "x \<in> set_btree tt"
        then have x_in_t: "x \<in> set_btree t" by (simp add: t_node)
        fix sepa assume "sepa \<in> set (separators (mts @ (mt, sep) # tts))"
        then have "sepa \<in> set (separators mts) \<or> sepa = sep \<or> sepa \<in> set (separators tts)"
          using separators_split by auto
        then show "sepa < x" using x_in_t
          apply (elim disjE)
            apply (metis (no_types, lifting) Un_iff assms(3) dual_order.strict_trans list.set_intros(1) separators_in_set set_append sorted_btree.simps(2) sorted_sub_sep_impl sub_node sub_sep_cons.simps subsetD)
          using assms(3) sorted_sub_sep_impl apply blast
          using \<open>x \<in> set_btree tt\<close> assms(3) sorted_btree.simps(2) t_node apply blast
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
        have "sorted_btree (Node ls u)"
          unfolding sorted_btree.simps
          using assms T_i sorted_node_i sorted_wrt_append sub_sorted_lr
        proof (safe)
          fix lsep assume "lsep \<in> set (separators ls)"
          fix x assume "x \<in> set_btree u"
          then have "x \<in> set_btree t \<or> x \<in> set_btree sub \<or> x = sep"
            using set_node_i T_i by auto
          then show "lsep < x"
            apply(elim disjE)
            using \<open>lsep \<in> set (separators ls)\<close> assms(3) apply simp
            using \<open>lsep \<in> set (separators ls)\<close> assms(3) sorted_btree.simps(2) sorted_btree_split_ls apply blast
            using \<open>lsep \<in> set (separators ls)\<close> assms(3) sorted_btree_split_ls apply blast
            done
        qed auto
        then show ?thesis
          using T_i assms(3) Nil sub_node t_node by auto
      next
        case (Up_i l a r)
        then have set_lar:
          "set_btree l \<subseteq> set_btree sub \<union> set_btree t \<union> {sep}"
          "a \<in> set_btree sub \<union> set_btree t \<union> {sep}"
          "set_btree r \<subseteq> set_btree sub \<union> set_btree t \<union> {sep}"
          using set_node_i by auto
        have "sorted_btree (Node (ls@[(l,a)]) r)"
          unfolding sorted_btree.simps
          using Up_i sorted_node_i assms 
        proof(safe)
          show "sorted_wrt sub_sep_sm (ls @ [(l, a)])"
            unfolding sorted_wrt_split
          proof (safe)
            fix asub asep assume ls_split: "(asub,asep) \<in> set ls"
            then have "asep < a" using set_lar assms
              by (metis UnE Un_iff Un_iff insert_absorb insert_iff insert_not_empty set_append some_child_sub(2) sorted_btree.simps(2) sorted_btree_split_ls)
            moreover have "\<forall>x \<in> set_btree l. asep < x"
            proof
              fix x assume "x \<in> set_btree l"
              then have "x \<in> set_btree sub \<union> set_btree t \<union> {sep}"
                using set_lar by auto
              then show "asep < x" using assms ls_split
                by (metis Un_iff separators_split singletonD some_child_sub(2) sorted_btree.simps(2) sorted_btree_split_ls)
            qed
            ultimately show "sub_sep_sm (asub, asep) (l, a)" by simp
          qed (simp_all add: sub_sorted_lr)
        next
          fix lsub lsep assume "(lsub, lsep) \<in> set (ls @ [(l, a)])"
          then have "(lsub, lsep) \<in> set ls \<or> (lsub,lsep) = (l,a)"
            by auto
          then show "sub_sep_cons (lsub, lsep)"
            apply(elim disjE)
            using assms(3) sorted_btree.simps(2) sorted_btree_split_ls apply blast
            using Up_i sorted_node_i by auto
        next
          fix sep assume "sep \<in> set (separators (ls @ [(l, a)]))"
          then have "sep \<in> set (separators ls) \<or> sep = a"
            by auto
          then have "\<forall>x \<in> set_btree r. sep < x"
            apply(elim disjE)
            using set_lar assms
             apply (metis (no_types, lifting) Un_iff Un_insert_right dual_order.strict_trans insert_iff sorted_btree.simps(2) sorted_btree_split_ls sorted_sub_sep_impl subsetD sup_bot.right_neutral)
            using sorted_node_i Up_i
            apply simp
            done
          then show "\<And>x. x \<in> set_btree r \<Longrightarrow> sep < x"
            by simp
        qed auto
        then show ?thesis
          using False Up_i Nil sub_node t_node by auto
      qed
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split[simp]:"r = (rsub,rsep)" by (cases r)
      then obtain rts rt where rsub_node[simp]: "rsub = Node rts rt"
        using assms Cons height_Leaf Suc by (cases rsub) simp
      then have
        "set_up_i (node_i k (mts@(mt,sep)#rts) rt) = set_btree (Node (mts@(mt,sep)#rts) rt)"
        using node_i_set by (simp del: node_i.simps)
      also have "\<dots> = set_btree sub \<union> set_btree rsub \<union> {sep}"
        using  sub_node rsub_node by auto
      finally have set_node_i: "set_up_i (node_i k (mts@(mt,sep)#rts) rt) = set_btree sub \<union> set_btree rsub \<union> {sep}"
        by simp

      have "sorted_btree (Node (mts@(mt,sep)#rts) rt)" unfolding sorted_btree.simps
        using assms(3) sub_node Cons
      proof (safe)
        show "sorted_wrt sub_sep_sm (mts @ (mt, sep) # rts)"
          unfolding sorted_wrt_split
        proof(safe)
          show "sorted_wrt sub_sep_sm mts" "sorted_wrt sub_sep_sm rts"
            using assms sub_node assms(3) Cons by auto
        next
          fix a b assume "(a, b) \<in> set mts"
          then show "sub_sep_sm (a, b) (mt, sep)"
            using subtree_in_subtrees 
            by (metis (no_types) Un_iff assms(3) list.set_intros(1) separators_in_set set_append some_child_sub(2) sorted_btree.simps(2) sub_node sub_sep_cons.simps sub_sep_sm.simps subsetD)
        next
          fix a b assume "(a, b) \<in> set rts"
          then have "sep < b"
            using assms sub_sorted_lr(3)
            by (metis list.set_intros(1) Cons r_split rsub_node separators_in_set some_child_sub(1) some_child_sub(2) sorted_wrt_sorted_left subsetD)
          moreover have "\<forall>y \<in> set_btree a. sep < y"
            using assms sub_sorted_lr(3)
            by (metis \<open>(a, b) \<in> set rts\<close> list.set_intros(1) Cons r_split rsub_node sorted_r_forall sub_sep_sm.simps subtree_sub_sm(2))
          ultimately show "sub_sep_sm (mt, sep) (a, b)"
            by simp
        qed
      next
        fix a b assume "(a, b) \<in> set (mts @ (mt, sep) # rts)"
        show "sub_sep_cons (a,b)"
          by (metis (no_types, lifting) Cons_eq_appendI UnE UnI2 \<open>(a, b) \<in> set (mts @ (mt, sep) # rts)\<close> assms(3) in_set_conv_decomp_first list.set_intros(1) Cons r_split rsub_node set_ConsD set_append set_btree_split(2) sorted_btree.simps(2) sub_node sub_sep_cons.simps subtree_in_subtrees)
      next
        fix x assume "x \<in> set_btree rt"
        then have x_in_t: "x \<in> set_btree rsub" by simp
        fix sepa assume "sepa \<in> set (separators (mts @ (mt, sep) # rts))"
        then have "sepa \<in> set (separators mts) \<or> sepa = sep \<or> sepa \<in> set (separators rts)"
          using separators_split by auto
        then show "sepa < x" using x_in_t
          apply (elim disjE)
            apply (metis Un_iff assms(3) dual_order.strict_trans list.set_intros(1) Cons r_split separators_in_set set_append some_child_sub(1) sorted_btree.simps(2) sorted_wrt_append sorted_wrt_sorted_left sub_node sub_sep_cons.simps subsetD)
          using \<open>x \<in> set_btree rt\<close> assms(3)  sub_sorted_lr(3)  Cons by auto
      qed auto
      then have
        sorted_node_i: "sorted_up_i (node_i k (mts@(mt,sep)#rts) rt)"
        using node_i_sorted by blast
      then show ?thesis
      proof(cases "node_i k (mts@(mt,sep)#rts) rt")
        case (T_i u)
        have "sorted_btree (Node (ls@(u,rsep)#rs) t)"
          unfolding sorted_btree.simps
        proof (safe)
          show "sorted_wrt sub_sep_sm (ls @ (u, rsep) # rs)"
            unfolding sorted_wrt_split
          proof (safe)
            fix a b assume "(a,b) \<in> set ls"
            then show "sub_sep_sm (a, b) (u, rsep)"
              unfolding sub_sep_sm.simps
              apply (safe)
               apply (metis (no_types, lifting) \<open>(a, b) \<in> set ls\<close> assms(3) Cons r_split sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_split2 sub_sep_sm.simps sub_sep_sm_trans)
              apply (metis (no_types, lifting) T_i UnE \<open>(a, b) \<in> set ls\<close> set_node_i assms(3) less_trans Cons r_split set_up_i.simps(1) singletonD sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_split2 sub_sep_sm.simps)
              done
          next
            fix a b assume "(a,b) \<in> set rs"
            then show "sub_sep_sm (u, rsep) (a, b)"
              using Cons sub_sorted_lr(3) by auto
          next
            show "sorted_wrt sub_sep_sm ls" "sorted_wrt sub_sep_sm rs"
              using sub_sorted_lr Cons by auto
          qed
        next
          fix a b assume "(a, b) \<in> set (ls @ (u, rsep) # rs)"
          then have "(a,b) \<in> set ls \<or> (a,b) \<in> set rs \<or> (a,b) = (u,rsep)"
            by auto
          then show "sub_sep_cons (a,b)"
            using Cons sub_sorted_lr proof(elim disjE)
            assume "(a,b) = (u,rsep)"
            show "sub_sep_cons (a,b)"
              unfolding sub_sep_cons.simps
            proof
              have "\<forall>x \<in> set_btree sub. x < sep" using assms by auto
              fix x assume "x \<in> set_btree a"
              then have "x \<in> set_btree rsub \<or> x = sep \<or> x \<in> set_btree sub"
                using \<open>(a,b) = (u,rsep)\<close> T_i set_node_i by auto
              then show "x < b"           
                using sub_sorted_lr Cons \<open>\<forall>x \<in> set_btree sub. x < sep\<close> 
                  \<open>(a, b) = (u, rsep)\<close> assms(3) Cons sorted_wrt_split2 by auto
            qed
          qed auto
        next
          show "\<And>sep x. sep \<in> set (separators (ls @ (u, rsep) # rs)) \<Longrightarrow> x \<in> set_btree t \<Longrightarrow> sep < x"
            using  assms Cons by auto (* this is slow *)
          show "\<And>x. x \<in> set (subtrees (ls @ (u, rsep) # rs)) \<Longrightarrow> sorted_btree x"
            using assms Cons sorted_node_i T_i by auto (* this is slow *)
          show "sorted_btree t" using assms by auto
        qed
        then show ?thesis
          using t_node T_i Cons sub_node False
          by (auto simp del: sorted_btree.simps node_i.simps)
      next
        case (Up_i l a r)
        then have set_node_i: 
          "set_up_i (Up_i l a r) = set_btree sub \<union> set_btree rsub \<union> {sep}"
          using set_node_i by auto

        have "sorted_btree (Node (ls@(l,a)#(r,rsep)#rs) t)"
          unfolding sorted_btree.simps
        proof (safe)
          show "sorted_wrt sub_sep_sm (ls @ (l, a) # (r, rsep) # rs)"
            unfolding sorted_wrt_split2
          proof (safe)
            fix lsub lsep assume "(lsub,lsep) \<in> set ls"
            show "sub_sep_sm (lsub,lsep) (l,a)"
              unfolding sub_sep_sm.simps
            proof -
              have "\<forall>x \<in> set_btree sub \<union> set_btree rsub \<union> {sep}. lsep < x"
                by (metis (no_types, lifting) UnE \<open>(lsub, lsep) \<in> set ls\<close> assms(3) less_trans Cons r_split singleton_iff sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_split2 sub_sep_sm.simps)
              then show "lsep < a \<and> Ball (set_btree l) ((<) lsep)"
                by (metis Un_iff set_node_i set_up_i.simps(2) singletonI)
            qed
          next
            fix rrsub rrsep assume "(rrsub, rrsep) \<in> set rs"
            then show "sub_sep_sm (r,rsep) (rrsub,rrsep)"
              using sub_sorted_lr Cons by fastforce
          next
            show "sub_sep_sm (l, a) (r, rsep)"
              unfolding sub_sep_sm.simps
            proof(safe)
              have "\<forall>x \<in> set_btree sub \<union> set_btree rsub \<union> {sep}. x < rsep"
                using sub_sorted_lr Cons
                by (metis UnE assms(3) ball_empty dual_order.strict_trans insert_iff less_irrefl list.set_intros(1) r_split sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_split2 sub_sep_cons.simps sub_sep_sm.simps)
              then show "a < rsep"
                using set_node_i by auto
            next
              show "\<And>x. x \<in> set_btree r \<Longrightarrow> a < x"
                using sorted_node_i Up_i by auto
            qed
          next
            show "sorted_wrt sub_sep_sm ls" "sorted_wrt sub_sep_sm rs"
              using sub_sorted_lr Cons by auto
          qed
        next
          have "\<forall>x \<in> set_btree sub \<union> set_btree rsub \<union> {sep}. x < rsep"
            using sub_sorted_lr Cons
            by (metis UnE assms(3) ball_empty dual_order.strict_trans insert_iff less_irrefl list.set_intros(1) r_split sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_split2 sub_sep_cons.simps sub_sep_sm.simps)
          then have "sub_sep_cons (r, rsep)"
            using set_node_i by auto

          fix ssub ssep assume "(ssub, ssep) \<in> set (ls @ (l, a) # (r, rsep) # rs)"
          then show "sub_sep_cons (ssub,ssep)"
            using sub_sorted_lr \<open>sub_sep_cons (r,rsep)\<close> sorted_node_i Up_i Cons
            by auto
        next
          fix ssep assume "ssep \<in> set (separators (ls @ (l, a) # (r, rsep) # rs))"
          then have "ssep \<in> set (separators ls) \<or> ssep = a \<or> ssep = rsep \<or> ssep \<in> set (separators rs)"
            using separators_split by auto
          then show "\<And>x. x \<in> set_btree t \<Longrightarrow> ssep < x"
            using assms Cons proof (elim disjE)
            fix x assume "x \<in> set_btree t"
            then have "rsep < x" "sep < x"
              using assms(3) Cons by auto
            then have  "\<forall>y \<in> set_btree sub. y < x" "\<forall>y \<in> set_btree rsub. y < x"
              using sub_sorted_lr(6) apply auto[1]
              by (metis \<open>rsep < x\<close> dual_order.strict_trans list.set_intros(1) Cons r_split sub_sep_cons.simps sub_sorted_lr(5))
            then have "a < x"
              by (metis Un_iff Un_insert_right \<open>x \<in> set_btree t\<close> assms(3) insertI1 set_node_i separators_split set_up_i.simps(2) sorted_btree.simps(2))
            then show "ssep = a \<Longrightarrow> ssep < x" "ssep = rsep \<Longrightarrow> ssep < x"
              using \<open>rsep < x\<close> by simp_all
          qed auto
        next
          fix x assume "x \<in> set (subtrees (ls@(l,a)#(r,rsep)#rs))"
          then have "x \<in> set (subtrees ls) \<or> x \<in> set (subtrees rs) \<or> x = l \<or> x = r"
            by auto
          then show "sorted_btree x"
            apply(elim disjE)
            using assms(3) Cons sorted_node_i Up_i by auto
        next
          show "sorted_btree t" using assms by simp
        qed
        then show ?thesis
          using Cons False Up_i sub_node t_node
          by auto
      qed
    qed
  qed simp
qed

lemma rebalance_last_tree_sorted: "\<lbrakk>sorted_btree (Node ts t); ts = ls@[(sub,sep)]; height sub = height t\<rbrakk>
\<Longrightarrow> sorted_btree (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_sorted by auto


find_theorems height split_max
lemma split_max_sorted: "\<lbrakk>split_max k t = (sub,sep); sorted_btree t; nonempty_lasttreebal t; t \<noteq> Leaf\<rbrakk>
\<Longrightarrow> sorted_btree sub"
proof (induction k t arbitrary: sub sep rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then obtain sub sep where last_split: "last ts = (sub,sep)"
      by (cases "last ts")
    have "sorted_btree (Node (butlast ts) sub)"
      unfolding sorted_btree.simps
      apply(safe)
          apply (metis "1.prems"(2) append_butlast_last_id butlast.simps(1) sorted_btree_sorted sorted_inorder_subsepsm sorted_wrt_append)
         apply (meson "1.prems"(2) in_set_butlastD sorted_btree.simps(2))
        apply (metis "1.prems"(3) Leaf btree.distinct(1) btree.set_cases fst_conv height_Leaf last_split nonempty_lasttreebal.simps(2) snoc_eq_iff_butlast)
      using "1.prems" apply auto[1]
      by (metis "1.prems"(3) Leaf fst_conv height_Leaf last_split nonempty_lasttreebal.simps(2) snoc_eq_iff_butlast sorted_btree.simps(1))      
    then show ?thesis
      using 1 Leaf last_split by auto
  next
    case (Node tts tt)
    then obtain s_sub s_max where sub_split: "split_max k t = (s_sub,s_max)"
      by (cases "split_max k t")
    then have "set_btree s_sub \<union> {s_max} = set_btree t"
      using split_max_set
      by (metis "1.prems"(3) Node btree.distinct(1) nonempty_lasttreebal.simps(2))
    moreover have "sorted_btree s_sub"
      using "1.prems"(2,3) "1.IH"[of tts tt s_sub s_max] Node sub_split
      by (auto simp del: split_max.simps)
    ultimately have "sorted_btree (Node ts s_sub)"
      using "1.prems" by auto
    then have "sorted_btree (rebalance_last_tree k ts s_sub)"
      using rebalance_last_tree_sorted
      by (metis "1.prems"(3) Node btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height sub_split)
    then show ?thesis
      using 1 Node sub_split
      by auto
  qed
qed simp

lemma btree_list_induct_pairs: "x \<in> set_btree_list ts = (\<exists>(sub,sep) \<in> set ts. x \<in> set_btree sub \<or> x = sep)"
  by (induction ts) (auto)

(* note this is kind of a duplicate of sorted_wrt_sorted_right2 *)
lemma sorted_last_tree_max: 
  assumes "\<forall>x \<in> set ts. sub_sep_cons x"
    and "\<forall>x \<in> set (separators ts). x < (y::('a::linorder))"
  shows "\<forall>x \<in> set_btree_list ts. x < y"
proof -
  have "\<forall>(sub,sep) \<in> set ts. sep < y \<and> (\<forall>z \<in> set_btree sub. z < y)"
    using assms(1) assms(2) by fastforce
  then show ?thesis
    using btree_list_induct_pairs by auto
qed



lemma split_max_max: "\<lbrakk>split_max k t = (sub,sep); sorted_btree t; nonempty_lasttreebal t; t \<noteq> Leaf\<rbrakk>
\<Longrightarrow> \<forall>x \<in> set_btree sub. x < sep"
proof (induction k t arbitrary: sub sep rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then obtain sub sep where last_split: "last ts = (sub,sep)"
      by (cases "last ts")
    then have "ts = butlast ts@[(sub,sep)]"
      using "1.prems"(3) by auto
    then have "\<forall>x \<in> set_btree (Node (butlast ts) sub). x < sep"
      by (metis "1.prems"(2) sorted_btree.simps(2) sorted_wrt_sorted_right2)
    then show ?thesis
      using "1.prems"(1) Leaf last_split by auto
  next
    case (Node tts tt)
    then obtain s_sub s_max where sub_split: "split_max k t = (s_sub,s_max)"
      by (cases "split_max k t")
    then have "set_btree s_sub \<union> {s_max} = set_btree t"
      using split_max_set
      by (metis "1.prems"(3) Node btree.distinct(1) nonempty_lasttreebal.simps(2))
    moreover have "\<forall>x \<in> set_btree s_sub. x < s_max"
      by (metis "1.IH" "1.prems"(2) "1.prems"(3) Un_iff btree.set_cases btree.simps(14) calculation empty_iff nonempty_lasttreebal.simps(2) sorted_btree.simps(2) sub_split)
    ultimately have "\<forall>x \<in> set_btree_list ts. x < s_max"
      by (metis (mono_tags, lifting) "1.prems"(2) Un_iff singletonI sorted_btree.simps(2) sorted_last_tree_max)
    then have "\<forall>x \<in> set_btree (Node ts s_sub). x < s_max"
      using \<open>\<forall>x\<in>set_btree s_sub. x < s_max\<close> by auto
    then have "\<forall>x \<in> set_btree (rebalance_last_tree k ts s_sub). x < s_max"
      using rebalance_last_tree_set split_max_height sub_split
      by (metis "1.prems"(3) Node btree.distinct(1) nonempty_lasttreebal.simps(2))
    then show ?thesis
      using 1 Node sub_split by auto
  qed
qed simp


lemma del_sorted: "\<lbrakk>k > 0; root_order k t; bal t; sorted_btree t\<rbrakk> \<Longrightarrow> sorted_btree (del k x t)"
proof (induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split_fun ts x = (ls,list)"
    by (cases "split_fun ts x")
  then show ?case
  proof(cases list)
    case Nil
    then have "sorted_btree (del k x t)"
      using 2 list_split Nil
      by (simp add: order_impl_root_order)
    moreover have "set_btree (del k x t) = set_btree t - {x}"
      using del_set
      by (meson "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(4) bal.simps(2) order_impl_root_order root_order.simps(2) sorted_btree.simps(2))
    ultimately have "sorted_btree (Node ts (del k x t))"
      using "2.prems"(4) by auto
    then have "sorted_btree (rebalance_last_tree k ts (del k x t))"
      by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal order_impl_root_order rebalance_last_tree_sorted root_order.simps(2) del_height)
    then show ?thesis
      using list_split Nil split_fun_req_alt(1) by force
  next
    case (Cons a rs)
    then obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    then have node_sorted_split: 
      "sorted_btree (Node (ls@(sub,sep)#rs) t)"
      "root_order k (Node (ls@(sub,sep)#rs) t)"
      "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems" list_split Cons split_fun_req_alt(1) by blast+
    consider (sep_n_x) "sep \<noteq> x" | (sep_x_Leaf) "sep = x \<and> sub = Leaf" |  (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have "set_btree (del k x sub) = set_btree sub - {x}"
        using del_set
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(4) a_split bal.simps(2) list_split Cons order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_btree.simps(2) split_fun_set(1))
      moreover have "sorted_btree (del k x sub)"
        by (metis "2"(2) "2.prems"(1) "2.prems"(2) "2.prems"(3) "2.prems"(4) sep_n_x  a_split bal.simps(2) list_split Cons order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_btree.simps(2) split_fun_set(1))
      ultimately have "sorted_btree (Node (ls@(del k x sub,sep)#rs) t)"
        unfolding sorted_btree.simps
        apply(safe)
        using replace_subtree_sorted_wrt node_sorted_split
            apply (metis Diff_subset sorted_btree.simps(2))
           apply (metis (no_types, lifting) DiffD1 Un_iff insert_iff list.simps(15) node_sorted_split(1) set_append sorted_btree.simps(2) sub_sep_cons.simps)
          apply (metis node_sorted_split(1) separators_split sorted_btree.simps(2))
         apply (metis Un_iff insert_iff node_sorted_split(1) sorted_btree.simps(2) subtrees_split)
        using node_sorted_split(1) sorted_btree.simps(2) by blast
      moreover have "height (del k x sub) = height t"
        using del_height
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) list_split Cons order_impl_root_order root_order.simps(2) split_fun_req_alt(1) subtree_in_subtrees)
      ultimately have "sorted_btree (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_sorted
        by (metis "2.prems"(3) bal_sub_height list_split Cons split_fun_req_alt(1))
      then show ?thesis
        using sep_n_x 2 Cons list_split a_split by simp
    next
      case sep_x_Leaf
      then have "sorted_btree (Node (ls@rs) t)"
        using remove_section_sorted node_sorted_split by blast
      then show ?thesis
        using sep_x_Leaf 2 Cons list_split a_split by simp
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      obtain s_sub s_max where sub_split: "split_max k sub = (s_sub, s_max)"
        by (cases "split_max k sub")
      then have split_results:
        "sub_sep_cons (s_sub, s_max)"
        "set_btree s_sub \<union> {s_max} = set_btree sub"
        "sorted_btree s_sub"
        using split_max_max split_max_set node_sorted_split split_max_sorted
        by (metis "2.prems"(1) bal.simps(2) btree.distinct(1) order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) sorted_btree.simps(2) sub_node sub_sep_cons.elims(3) subtree_in_subtrees)+
      have "sorted_btree (Node (ls@(s_sub,s_max)#rs) t)"
        unfolding sorted_btree.simps
      proof (safe)
        show "sorted_wrt sub_sep_sm (ls @ (s_sub, s_max) # rs)"
          using split_results node_sorted_split replace_subtree_sorted_wrt2
          by (metis "2.prems"(4) Un_insert_right a_split insertI1 list_split Cons sorted_btree.simps(2) split_fun_set(1) sup.cobounded1)
      next
        show "\<And>a b. (a, b) \<in> set (ls @ (s_sub, s_max) # rs) \<Longrightarrow> sub_sep_cons (a, b)"
          using split_results node_sorted_split
          by (metis Un_iff insert_iff list.simps(15) set_append sorted_btree.simps(2))
      next
        have "s_max < sep"
          using a_split list_split Cons node_sorted_split(1) split_fun_req_alt(1) split_results(2) by fastforce
        then have "\<forall>x \<in> set_btree t. s_max < x" using node_sorted_split(1)
          by auto
        then show "\<And>sep x. sep \<in> set (separators (ls @ (s_sub, s_max) # rs)) \<Longrightarrow> x \<in> set_btree t \<Longrightarrow> sep < x"
          using node_sorted_split(1) by auto
      next
        show "\<And>x. x \<in> set (subtrees (ls @ (s_sub, s_max) # rs)) \<Longrightarrow> sorted_btree x"
          using node_sorted_split(1) split_results(3) by auto
        show "sorted_btree t"
          using node_sorted_split(1) by auto
      qed
      moreover have "height s_sub = height t"
        using split_max_height node_sorted_split
        by (metis "2.prems"(1) sub_split bal.simps(2) btree.distinct(1) order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) sub_node subtree_in_subtrees)
      ultimately have "sorted_btree (rebalance_middle_tree k ls s_sub s_max rs t)"
        using rebalance_middle_tree_sorted node_sorted_split
        by (metis bal_sub_height)
      then show ?thesis
        using sep_x_Node 2 Cons list_split a_split sub_split
        by auto
    qed
  qed
qed simp


lemma reduce_root_order: "\<lbrakk>k > 0; almost_order k t\<rbrakk> \<Longrightarrow> root_order k (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits simp add: order_impl_root_order)
  done

lemma reduce_root_bal: "bal (reduce_root t) = bal t"
  apply(cases t)
   apply(auto split!: list.splits)
  done

lemma reduce_root_set: "set_btree (reduce_root t) = set_btree t"
  apply(cases t)
   apply(simp)
  subgoal for ts t
    apply(cases ts)
     apply(auto)
    done
  done

lemma reduce_root_sorted: "sorted_btree (reduce_root t) = sorted_btree t"
  apply(cases t)
   apply(auto split!: list.splits)
  done


lemma delete_order: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> root_order k (delete k x t)"
  using del_order
  by (simp add: reduce_root_order)

lemma delete_bal: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> bal (delete k x t)"
  using del_bal
  by (simp add: reduce_root_bal)

lemma delete_set: "\<lbrakk>k > 0; bal t; root_order k t; sorted_btree t\<rbrakk> \<Longrightarrow> set_btree (delete k x t) = set_btree t - {x}"
  using del_set
  by (simp add: reduce_root_set)

lemma delete_sorted: "\<lbrakk>k > 0; bal t; root_order k t; sorted_btree t\<rbrakk> \<Longrightarrow> sorted_btree (delete k x t)"
  using del_sorted
  by (simp add: reduce_root_sorted)

(* preparation for set specification *)

fun invar where "invar k t = (bal t \<and> root_order k t \<and> sorted_btree t)"

definition "empty_btree = Leaf"

(* TODO (opt) runtime wrt runtime of split_fun *)

(* we are interested in a) number of comparisons b) number of fetches c) number of writes *)
(* a) is dependent on t_split_fun, the remainder is not (we assume the number of fetches and writes
for split fun is 0 *)


(* TODO simpler induction schemes /less boilerplate isabelle/src/HOL/ex/Induction_Schema *)

(* Alternative Set spec *)
text "We show that BTrees of order k > 0 fulfill the Set specifications."
interpretation S: Set
  where empty = empty_btree and isin = isin and insert = "insert (Suc k)" and delete = "delete (Suc k)"
    and set = set_btree and invar = "invar (Suc k)"
proof (standard, goal_cases)
  case (2 s x)
  then show ?case
    by (simp add: isin_set)
next
  case (3 s x)
  then show ?case using insert_set
    by simp
next
  case (4 s x)
  then show ?case using delete_set
    by auto
next
  case (6 s x)
  then show ?case using insert_order insert_sorted insert_bal
    by auto
next
  case (7 s x)
  then show ?case using delete_order delete_sorted delete_bal
    by auto
qed (simp add: empty_btree_def)+

end


text "Finally we show that the split_fun axioms are feasible by providing an example split function"

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

unused_thms

interpretation btree_linear_search: split_fun linear_split
  by (simp add: linear_split_req linear_split_append split_fun_def)


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

value "cmp (1::nat) 2"


fun binary_split where
  "binary_split as x = binary_split_help [] as [] x"

value "cmp (1::nat) 2"

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
      apply auto
    oops


(* TODO some examples to show that the implementation works and lemmas make sense *)
    find_theorems sorted_wrt
lemmas [code] = btree_linear_search.insert.simps

value "Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf"
value "root_order 10 (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"
value "bal (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"
thm btree_linear_search.insert.simps
  (* BREAKS: no code generated *)
  (*value "btree_linear_search.insert 5 10 (Node [(Leaf,(1::nat)),(Leaf,2),(Leaf,3)] Leaf)"*)



end