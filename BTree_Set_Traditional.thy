theory BTree_Set_Traditional
  imports BTree_Set
begin

(* For documentation purposes, the traditional way proofs
for the Set-Interface (by direct proof of set and sortedness properties)
is included below 

it appears that for some reason, removing "node_i.simps" does not work anymore
*)


(* idea: make sorted_list a sorted_wrt *)
find_theorems sorted_wrt
thm sorted_wrt_append

fun sub_sep_sm where
  "sub_sep_sm (sub_l, sep_l) (sub_r, sep_r) = (
    (sep_l < sep_r) \<and>
    (\<forall>x \<in> set_btree sub_r. sep_l < x)
  )"

fun sub_sep_cons where
  "sub_sep_cons (sub, sep) = (
    \<forall>x \<in> set_btree sub. x < sep
  )"

subsection "sortedness"

fun sorted_btree where
  "sorted_btree Leaf = True" |
  "sorted_btree (Node ts t) = (
    sorted_wrt sub_sep_sm ts \<and>
    (\<forall>x \<in> set ts. sub_sep_cons x) \<and>
    (\<forall>sep \<in> set (separators ts). \<forall>y \<in> set_btree t. sep < y) \<and>
    (\<forall>sub \<in> set (subtrees ts). sorted_btree sub) \<and>
    sorted_btree t
  )"

value "sorted_less (inorder (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf))"
value "sorted_btree (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf)"


lemma sorted_wrt_list_sorted: "sorted_wrt sub_sep_sm xs \<Longrightarrow> sorted_less (separators xs)"
  by (induction xs) (auto)


lemma sorted_wrt_sorted_left: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> t \<in> set (subtrees xs) \<Longrightarrow> \<forall>x \<in> set_btree t. x > sep"
  by auto


lemma sorted_wrt_sorted_left2: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> x \<in> set (separators xs) \<Longrightarrow> x > sep"
  by auto

(* the below is independent of the inter-pair sorting *)
lemma sorted_wrt_sorted_right: "\<forall>x \<in> set xs. sub_sep_cons x \<Longrightarrow> (t, sep) \<in> set xs \<Longrightarrow> \<forall>x \<in> set_btree t. x < sep"
  by auto

find_theorems sorted_wrt "(@)"

(* this works only for linear orders *)
lemma sorted_wrt_sorted_right2: "
sorted_wrt sub_sep_sm ((ls@(sub,sep)#rs)::('a::linorder) btree_list) \<Longrightarrow> (\<forall>x \<in> set (ls@(sub,sep)#rs). sub_sep_cons x) \<Longrightarrow>
 (\<forall>x \<in> set_btree (Node ls sub). x < sep)"
  apply (auto simp add: sorted_wrt_append)
  by (meson UnI1 dual_order.strict_trans sub_sep_cons.simps sub_sep_sm.simps)

lemma sorted_pair_list:
  "(sorted_less (inorder sub) \<and> (\<forall>x \<in> set (inorder sub). x < sep)) = sorted_less((inorder sub) @ [sep])"
  using sorted_snoc_iff
  by auto


lemma sorted_wrt_split: "sorted_wrt sub_sep_sm (l@(a,(b::('a::linorder)))#r) =
   (sorted_wrt sub_sep_sm l \<and>
    sorted_wrt sub_sep_sm r \<and>
(\<forall>x \<in> set l. sub_sep_sm x (a,b)) \<and>
(\<forall>x \<in> set r. sub_sep_sm (a,b) x))"
  using sorted_wrt_append by fastforce



lemma sorted_r_forall: "sorted_wrt P (a#rs) \<Longrightarrow> \<forall>y \<in> set rs. P a y"
  by simp

lemma sorted_l_forall: "sorted_wrt P (ls@[a]) \<Longrightarrow> \<forall>y \<in> set ls. P y a"
  by (simp add: sorted_wrt_append)


lemma sub_sep_sm_trans:
  "\<lbrakk>sub_sep_sm (a::('a::linorder) btree_pair) b; sub_sep_sm b c\<rbrakk> \<Longrightarrow> sub_sep_sm a c"
  apply(cases a)
  apply(cases b)
  apply(cases c)
  apply(auto)
  done

find_theorems sorted_wrt

lemma sorted_wrt_split2: "sorted_wrt sub_sep_sm ((l@(a,b)#(c,d)#r)::('a::linorder) btree_list) =
   (sorted_wrt sub_sep_sm l \<and>
    sorted_wrt sub_sep_sm r \<and>
(\<forall>x \<in> set l. sub_sep_sm x (a,b)) \<and>
(\<forall>x \<in> set r. sub_sep_sm (c,d) x) \<and>
sub_sep_sm (a,b) (c,d))"
  unfolding sorted_wrt_append
  by fastforce


lemma replace_subtree_sorted_wrt:
  assumes "sorted_wrt sub_sep_sm ((ls@(sub,sep)#rs)::('a::linorder) btree_list)"
    and "set_btree sub2 \<subseteq> set_btree sub"
  shows "sorted_wrt sub_sep_sm (ls@(sub2,sep)#rs)"
  unfolding sorted_wrt_split
  using assms sorted_wrt_split by fastforce


lemma replace_subtree_sorted_wrt2:
  assumes "sorted_wrt sub_sep_sm ((ls@(sub,sep)#rs)::('a::linorder) btree_list)"
    and "set_btree sub2 \<subseteq> set_btree sub"
    and "sep2 \<in> set_btree sub"
    and "sub_sep_cons (sub,sep)"
  shows "sorted_wrt sub_sep_sm (ls@(sub2,sep2)#rs)"
  unfolding sorted_wrt_split
  apply(safe)
  using assms(1) sorted_wrt_split apply blast
  using assms(1) sorted_wrt_split apply blast
   apply (metis (no_types, lifting) assms(1,2,3) sorted_wrt_split sub_sep_sm.simps subset_eq)
  by (metis assms(1,3,4) dual_order.strict_trans sorted_r_forall sorted_wrt_append sub_sep_cons.simps sub_sep_sm.simps)


lemma remove_section_sorted:
  assumes "sorted_btree (Node (ls@x#rs) t)"
  shows "sorted_btree (Node (ls@rs) t)"
  unfolding sorted_btree.simps
  apply(safe)
      apply (metis (no_types, lifting) assms list.set_intros(2) sorted_btree.simps(2) sorted_wrt_Cons sorted_wrt_append)
     apply (metis Un_iff assms list.set_intros(2) set_append sorted_btree.simps(2))
  using assms
  by auto


lemma sorted_btree_sorted: "sorted_btree t \<Longrightarrow> sorted_less (inorder t)"
proof(induction t rule: sorted_btree.induct)
  case (2 ts t)
  then have "\<lbrakk>sorted_btree (Node ts t)\<rbrakk> \<Longrightarrow> sorted_less (inorder (Node ts t))"
  proof (induction ts)
    case (Cons a list)
    then have Cons_help: 
      "sorted_wrt sub_sep_sm list" 
      "\<forall>x \<in> set list. sub_sep_cons x"
      "\<forall>sub \<in> set (subtrees list). sorted_btree sub"
      by (simp_all)
    then have "sorted_btree (Node list t)" using Cons
      by simp
    then have Cons_sorted: "sorted_less (inorder (Node list t))"
      using Cons.IH Cons.prems(2) 2 by auto

    from Cons obtain sub sep where pair_a: "a = (sub,sep)"
      by (cases a)
    then have "sorted_btree sub" using 2 Cons
      by simp
    then have "sorted_less (inorder sub)" using 2 Cons pair_a
      by force

    from pair_a have "\<forall>x \<in> set (separators list). sep < x"
      using sorted_wrt_Cons sorted_wrt_list_sorted Cons_help
      by (metis (no_types, lifting) Cons.prems(1) list.simps(9)  snd_conv sorted_btree.simps(2))
    moreover have "\<forall>t \<in> set (subtrees list). (\<forall>x \<in> set_btree t. sep < x)"
      using pair_a Cons sorted_btree.simps(2) sorted_wrt_sorted_left by metis
    ultimately have "\<forall>x \<in> set_btree (Node list t). sep < x"
      using Cons.prems(1) pair_a by auto
    then have sep_sm: "\<forall>x \<in> set (inorder (Node list t)). sep < x"
      using set_btree_inorder[of "Node list t"]
      by simp
    then have "sorted_less (sep # inorder (Node list t))"
      using Cons_sorted sorted_Cons_iff by blast
    moreover have "\<forall>y \<in> set (inorder sub). \<forall>x \<in> set (inorder (Node list t)). y < x"
      using Cons_help sep_sm pair_a Cons
      by (metis dual_order.strict_trans list.set_intros(1) set_btree_inorder sorted_btree.simps(2) sub_sep_cons.simps)
    ultimately have "sorted_less (inorder sub @ sep # inorder (Node list t))"
      using sorted_wrt_append[of "(<)" "inorder sub" "sep # inorder (Node list t)"] \<open>sorted_less (inorder (Node list t))\<close>
      by (metis Cons.prems(1) \<open>sorted_less (inorder sub)\<close> list.set_intros(1) pair_a set_btree_inorder sorted_btree.simps(2) sorted_mid_iff sorted_pair_list sub_sep_cons.simps)
    then have "sorted_less ((inorder sub @ [sep]) @ inorder (Node list t))"
      by simp
    then have "sorted_less ((\<lambda>(sub, sep). BTree.inorder sub @ [sep]) a @ foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) list) [] @ inorder t)"
      by (simp add: concat_conv_foldr pair_a)
    then have "sorted_less (foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) (a#list)) [] @ inorder t)" 
      by simp
    then show ?case
      by (simp add: concat_conv_foldr)
  qed auto
  then show ?case using 2 by auto
qed auto

lemma sorted_inorder_list_subtrees:
  "sorted_less (inorder_list ts) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
proof(induction ts)
  case (Cons a ts)
  then obtain sub sep where "a = (sub,sep)"
    by (cases a)
  then have "sorted_less (inorder sub)"
    using Cons by (simp add: sorted_wrt_append)
  moreover have "set (subtrees (a#ts)) = set (subtrees ts) \<union> {sub}"
    using \<open>a = (sub,sep)\<close> by auto
  moreover have "sorted_less (inorder_list ts)"
    using Cons.prems sorted_wrt_append by fastforce
  ultimately show ?case using Cons
    by auto
qed auto

corollary sorted_inorder_subtrees: "sorted_less (inorder (Node ts t)) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  using sorted_inorder_list_subtrees sorted_wrt_append by auto

lemma sorted_inorder_subtrees_induct:
  "sorted_less (inorder_list (ls@(sub,sep)#rs)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_last: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder t)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_list_subcons: "sorted_less (inorder_list ts) \<Longrightarrow> \<forall>x \<in> set ts. sub_sep_cons x"
proof(induction ts)
  case (Cons a ts)
  then obtain sub sep where "a = (sub,sep)"
    by (cases a)
  then have "sorted_less (inorder sub @ [sep])"
    using Cons by (simp add: sorted_wrt_append)
  then have "sub_sep_cons (sub,sep)"
    unfolding sub_sep_cons.simps
    using set_btree_inorder sorted_pair_list
    by fastforce
  moreover have "sorted_less (inorder_list ts)"
    using Cons.prems sorted_wrt_append by fastforce
  ultimately show ?case using Cons         
    using \<open>a = (sub,sep)\<close> by auto
qed auto

corollary sorted_inorder_subcons: "sorted_less (inorder (Node ts t)) \<Longrightarrow> \<forall>x \<in> set ts. sub_sep_cons x"
  using sorted_inorder_list_subcons sorted_wrt_append by auto

lemma sorted_inorder_fold: "sorted_less (inorder (Node ts t)) \<Longrightarrow> (\<forall>x \<in> set (inorder_list ts). \<forall>y \<in> set (inorder t). x < y)"
  apply(induction ts)
   apply (simp add: sorted_Cons_iff sorted_wrt_append)+
  by blast

lemma separators_subset: "set (separators xs) \<subseteq> set (inorder_list xs)"
  apply(induction xs)
   apply(auto)
  done

lemma sorted_inorder_seps: "sorted_less (inorder (Node ts t)) \<Longrightarrow> (\<forall>sep \<in> set (separators ts). \<forall>y \<in> set (inorder t). sep < y)"
  using sorted_inorder_fold separators_subset by fastforce

lemma sorted_inorder_impl_list: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder_list ts)"
  by (simp add: sorted_wrt_append)

lemma set_inorder_btree: "set (inorder t) = set_btree t"
  apply(induction t)
   apply auto
  done

lemma set_inorder_btree_list: "set (inorder_list xs) = set_btree_list xs"
  by (auto simp add: set_inorder_btree)

lemma sorted_inorder_list_subsepsm: "sorted_less (inorder_list ts) \<Longrightarrow> sorted_wrt sub_sep_sm ts"
proof (induction ts)
  case (Cons x list)
  then obtain sub sep where x_pair: "x = (sub, sep)" by (cases x)
  then have list_split: "inorder_list (x#list) = inorder sub @ sep # inorder_list list"
    unfolding inorder.simps by auto
  then have "sorted_less (inorder_list list)" 
    using  Cons.prems sorted_cons
    by (simp add: list_split sorted_wrt_append)
  then have sorted_wrt_rec: "sorted_wrt sub_sep_sm list" using Cons by auto

  from list_split have "\<forall>l \<in> set (inorder_list list). sep < l"
    by (metis (no_types, lifting) Cons.prems sorted_r_forall sorted_wrt_append)
  then have "\<forall>l \<in> set_btree_list list. sep < l"
    by (metis (mono_tags, lifting) set_inorder_btree_list)
  then have sorted_wrt_local: "\<forall>(sub_r, sep_r) \<in> set list. (sep < sep_r \<and> (\<forall>r \<in> set_btree sub_r. sep < r))"
    by (induction list) auto


  from sorted_wrt_local sorted_wrt_rec show ?case
    unfolding sorted_wrt.simps sub_sep_sm.simps
    using x_pair by auto
qed auto

corollary sorted_inorder_subsepsm: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_wrt sub_sep_sm ts"
  using sorted_inorder_impl_list sorted_inorder_list_subsepsm by blast


find_theorems sorted_less inorder

lemma sorted_sorted_btree: "sorted_less (inorder t) \<Longrightarrow> sorted_btree t"
  apply(induction t)
   apply(simp)
  unfolding sorted_btree.simps
  apply (safe)
  using sorted_inorder_subsepsm apply blast
  using sorted_inorder_subcons apply blast
  using sorted_inorder_seps set_btree_inorder apply fastforce
  using sorted_inorder_subtrees apply fastforce
  using sorted_inorder_last apply blast
  done

lemma sorted_btree_eq: "sorted_less (inorder t) = sorted_btree t"
  using sorted_btree_sorted sorted_sorted_btree by blast


context split_fun
begin




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

lemma split_fun_set_ls: "split_fun ts x = (ls,[]) \<Longrightarrow> set ls = set ts"
  using split_fun_req_alt by fastforce


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

subsection "insert Function"


lemma height_sub_merge: "height t = height s \<Longrightarrow> height (Node (ls@(t,a)#rs) tt) = height (Node (ls@(s,a)#rs) tt)"
  by simp

(* ins acts as a Set insertion *)

fun set_up_i where
  "set_up_i (T_i t) = set_btree t" |
  "set_up_i (Up_i l a r) = set_btree l \<union> set_btree r \<union> {a}"

thm BTree.set_btree_induct

lemma up_i_set: "set_up_i (Up_i (Node ls sub) sep (Node rs t)) = set_btree (Node (ls@(sub,sep)#rs) t)"
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
    using up_i_set append_take_drop_id
    by metis
  also have "\<dots> = set_up_i (node_i k ts t)"
    using False split_half_ts
    by simp
  finally show ?thesis
    by simp
qed simp


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
        by blast
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
          by blast
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
          apply (simp del: node_i.simps add: node_i_sorted)
          sorry (* FIXME this used to work *)
      qed
    qed
  qed
qed simp

(* wrapped up insert invariants *)

lemma tree_i_sorted: "sorted_up_i u \<Longrightarrow> sorted_btree (tree_i u)"
  apply(cases u)
  apply(auto)
  done

lemma tree_i_set: "set_up_i u = set_btree (tree_i u)"
  apply(cases u)
  apply(auto)
  done

lemma insert_sorted: "sorted_btree t \<Longrightarrow> sorted_btree (insert k x t)"
  using ins_sorted
  by (simp add: tree_i_sorted)

lemma insert_set: "set_btree t \<union> {x} = set_btree (insert k x t)"
  using ins_set
  by (simp add: tree_i_set)

section "Deletion"

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
        using node_i_set
        by blast
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
        using node_i_set (*former: by (simp del: node_i.simps) *) by blast
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
  assumes "split_max k t = (sub,sep)"
    and "nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "set_btree t = set_btree sub \<union> {sep}"
  using assms
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
        (*FIXME by (metis list.simps(5) sorted_btree.simps(2))+*)
      sorry
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
        using sorted_split_contains sep_n_x x_not_sub sub_set
      proof -
        have "set_btree t - {x} \<union> ({sep} - {x} \<union> (set_btree sub - {x} \<union> (set_btree_list ls - {x})) \<union> (set_btree_list rs - {x})) = set_btree t \<union> ({sep} \<union> (set_btree sub - {x} \<union> set_btree_list ls) \<union> set_btree_list rs)"
          using sep_n_x x_not_sub(1) x_not_sub(2) x_not_sub(3) by auto
        then show ?thesis
          using sub_set by auto
      qed
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


(* sortedness of delete, the hard way *)


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
        using node_i_set (* former by (simp del: node_i.simps) *) by blast
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


lemma delete_set: "\<lbrakk>k > 0; bal t; root_order k t; sorted_btree t\<rbrakk> \<Longrightarrow> set_btree (delete k x t) = set_btree t - {x}"
  using del_set
  by (simp add: reduce_root_set)

lemma delete_sorted: "\<lbrakk>k > 0; bal t; root_order k t; sorted_btree t\<rbrakk> \<Longrightarrow> sorted_btree (delete k x t)"
  using del_sorted
  by (simp add: reduce_root_sorted)


(* preparation for set specification *)

fun invar where "invar k t = (bal t \<and> root_order k t \<and> sorted_btree t)"

(* Traditional Set spec *)
text "We show that BTrees of order k > 0 fulfill the Set specifications."
interpretation S: Set
  where empty = Leaf and isin = isin and insert = "insert (Suc k)" and delete = "delete (Suc k)"
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
qed (simp)+

end

end