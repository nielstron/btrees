theory BTree                 
  imports Main "HOL-Data_Structures.Cmp"  "HOL-Data_Structures.Set_Specs"
begin

hide_const (open) Sorted_Less.sorted

abbreviation "sorted_less \<equiv> Sorted_Less.sorted"


subsection "General structure and concepts definition"

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"
  (* definition heavily based on Tree234_Set, Pair structure from popl10 (malecha)/mtps08*)

(*

   struct {
     key keys[10];
     node *nodes[11];
   } node;

   struct {
    key *keys;
    node **nodes;
   }
   
   
   'a list     'a set
   
   R xs s \<longleftrightarrow> s=set xs \<and> distinct xs
   
   member :: 'a \<Rightarrow> 'a list \<Rightarrow> bool     
   (\<in>) ::    'a \<Rightarrow> 'a set \<Rightarrow> bool
   
             ((=) \<rightarrow> R   \<rightarrow> (=)) member (\<in>)
   
   
   
   (=) xi x,  R si s  \<Longrightarrow> (=) (member xi si) ((\<in>) x s)
   
   
   (A \<rightarrow> B) f g \<longleftrightarrow> \<forall>x y. A x y \<longrightarrow> B (f x) (g y)
   
   
   
   R tree_ptr tree
   
   
   \<box> - empty heap
   
   ptr \<mapsto> x  - heap where ptr points to x
   
   
   A * B - combined heap described by A and B, parts are DISJOINT
   
   p\<^sub>1 \<mapsto> x * p\<^sub>2 \<mapsto> y
   
   
   
   \<forall>s F. (P ** F) s \<longrightarrow> \<exists>s'. run c s = SUCCESS r s' \<and> (Q r ** F) s'
   
   {P} c {\<lambda>r. Q r}
   
   
   \<up>\<phi> \<equiv> if \<phi> then \<box> else false
   
   
   'a M  =  heap \<Rightarrow> SUCC 'a heap | FAIL
   
   load :: 'a ptr \<Rightarrow> 'a M
   store :: 'a ptr \<Rightarrow> 'a \<Rightarrow> unit M
   
   { p \<mapsto> x } load p {\<lambda>r. \<up>(r=x) ** p \<mapsto> x }
   
   { p \<mapsto> y } store p x {\<lambda>_. p \<mapsto> x }
   
   
   {P} c {Q} \<Longrightarrow> {P**F} c {Q**F}
   

   return :: 'a \<Rightarrow> 'a M
   return x = \<lambda>h. SUCC x h       {\<box>} return x {\<lambda>r. r=x}
      
   (;) :: 'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M
   (x\<leftarrow>m; f x) s = case m s of FAIL \<Rightarrow> FAIL
                             | SUCC x s' \<Rightarrow> f x s'   
   

   f x \<equiv> ... f ...                                
   
   f \<equiv> rec ( \<lambda>f x. if x<1 then return 0 else f (x-1) )
   
   wf <
   \<And>x f t. (\<forall>x' t'. {P ** V t' ** t'<t} f x' {Q}) \<Longrightarrow> {P ** V t} F f x {Q}
   --------------------------------
   {P} rec F x {Q}
   
   
   assn_list R [] [] = \<box>
   assn_list R (x:xs) (y:ys) = R x y ** assn_list xs ys
   assn_list _ _ _ = false
   
   p\<mapsto>\<^sub>a[x\<^sub>1,...,x\<^sub>n] = p+0 \<mapsto> x\<^sub>1 ** ... ** p+(n-1) \<mapsto> x\<^sub>n
   
   assn_array R p xs = \<exists>xs'. p\<mapsto>\<^sub>axs' ** assn_list R xs' xs
   
   
   R :: 
   
   R p t
   
     R null Leaf
     
     R p (Node ts t) = p \<mapsto> (tsi,ti) ** R ti t ** assn_array (\<lambda>(subi,sepi) (sub,sep). R subi sub ** sepi=sep) ts tsi
   
     

*)


datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

type_synonym 'a btree_list =  "('a btree * 'a) list"
type_synonym 'a btree_pair =  "('a btree * 'a)"

fun inorder :: "'a btree \<Rightarrow> 'a list" where
  "inorder Leaf = []" |
  "inorder (Node ts t) = (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) []) @ inorder t"

fun inorder_list where
  "inorder_list ts = (foldr (@) (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) [])"

abbreviation subtrees where "subtrees xs \<equiv> (map fst xs)"
abbreviation seperators where "seperators xs \<equiv> (map snd xs)"
fun set_btree_pair where
  "set_btree_pair uu = (\<Union>(set_btree ` Basic_BNFs.fsts uu) \<union> Basic_BNFs.snds uu)"
fun set_btree_list where
  "set_btree_list ts = (\<Union>uu\<in>set ts. set_btree_pair uu)"


lemma set_btree_split: 
  "set_btree (Node (l@(sub,sep)#r) t) = set_btree (Node (l@r) t) \<union> set_btree sub \<union> {sep}"
  "set_btree (Node ts t) = set_btree_list ts \<union> set_btree t"
  "set_btree_list (ls@m#rs) = set_btree_list ls \<union> set_btree_pair m \<union> set_btree_list rs"
  "set_btree (Node (ls@m#rs) t) = set_btree_list ls \<union> set_btree_pair m \<union> set_btree_list rs \<union> set_btree t"
  by auto

class height =
  fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: (type) height
begin

fun height_btree :: "'a btree \<Rightarrow> nat" where
  "height Leaf = 0" |
  "height (Node ts t) = Suc (fold max (map height (subtrees ts)) (height t))"

instance ..

end

lemma height_Leaf: "height t = 0 \<longleftrightarrow> t = Leaf"
  by (induction t) (auto)

(* not sure if required but appearently already present for coding equivalence *)
lemma set_eq_fold: "fold max xs n = Max (set xs \<union> {n})"
  by (metis Max.set_eq_fold Un_insert_right list.simps(15) sup_bot.right_neutral)

thm btree.set

value "height_alt (Node [] (Leaf::nat btree))"
value "height (Node [] (Leaf::nat btree))"

lemma seperators_split:
  "set (seperators (l@(a,b)#r)) = set (seperators l) \<union> set (seperators r) \<union> {b}"
  by auto

lemma subtrees_split:
  "set (subtrees (l@(a,b)#r)) = set (subtrees l) \<union> set (subtrees r) \<union> {a}"
  by auto



lemma fold_max_max: "max (a::(_::linorder)) (fold max bs b) = fold max bs (max a b)"
  apply(induction bs arbitrary: a b)
   apply(auto simp add: max.left_commute)
  done

lemma max_sep_fold_max: "max (fold max as (a::(_::linorder))) (fold max bs b) = (fold max (as@a#bs) b)"
  apply(induction as arbitrary: a bs b)
   apply(auto simp add: max.assoc max.left_commute fold_max_max)
  done


lemma fold_max_extract:"fold max (l@a#r) n = max (a::_::linorder) (fold max (l@r) n)"
  apply(induction r arbitrary: l a n)
   apply(auto simp add: fold_max_max max.left_commute)
  done

lemma fold_max_append: "fold max bs (max (a::(_::linorder)) b) = fold max (bs@[a]) b"
  apply(induction bs arbitrary: a b)
   apply(auto simp add: max.left_commute)
  done

lemma height_btree_order:
  "height (Node (ls@[a]) t) = height (Node (a#ls) t)"
  apply(induction ls arbitrary: a t)
   apply(simp_all add: fold_max_max max.left_commute)
  done

lemma height_btree_swap: 
  "height (Node ((sub,x)#ls) t) = max (height (Node ls t)) (Suc (height sub))"
  by (auto simp add: fold_max_max max.commute)

lemma height_btree_swap2: 
  "height (Node ((sub,x)#ls) t) = max (height (Node ls sub)) (Suc (height t))"
  by (auto simp add: fold_max_max max.commute)

value "(Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"
value "inorder (Node [(Leaf, (1::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 10), (Leaf, 30), (Leaf, 100)] Leaf)"


lemma set_map_pred_eq: "(\<forall>x \<in> set (map f xs). P x) = (\<forall>x \<in> set xs. P (f x))"
  apply(induction xs)
   apply(auto)
  done


definition set_btree_inorder:: "'a btree \<Rightarrow> 'a set" where 
  "set_btree_inorder = set \<circ> inorder"

thm btree.simps
find_theorems set_btree
value "set_btree (Node [(Leaf, 1::nat)] Leaf)"


lemma append_foldr_set: "set (foldr (@) xs []) = \<Union> (set (map set xs))"
  apply(induction xs)
   apply(auto)
  done

lemma set_btree_inorder_set_btree: "set_btree_inorder t = set_btree t"
  apply(induction t)
   apply(auto simp add: set_btree_inorder_def append_foldr_set)
  done

lemma child_subset: "p \<in> set t \<Longrightarrow> set_btree (fst p) \<subseteq> set_btree (Node t n)"
  apply(induction p arbitrary: t n)
  apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
    and "sep \<in> set (seperators t)"
  using assms by force+ 


(* idea: we show that if any element is in the set_btree_inorder of a tree, then it must be in the list or in the subtree given by btree_list_choose,
show the latter by case distinction on the compare of btree_list *)

lemma set_btree_list_induct:
  "x \<in> set_btree_list ts = (x \<in> set (seperators ts) \<or> (\<exists>sub \<in> set (subtrees ts). x \<in> set_btree sub))"
  by (induction ts) auto

lemma set_btree_induct:
  "x \<in> set_btree (Node ts t) = (x \<in> set (seperators ts) \<or> (\<exists>sub \<in> set (subtrees ts). x \<in> set_btree sub) \<or> x \<in> set_btree t)"
  by (induction ts) auto


lemma seperators_in_set:
  "set (seperators ts) \<subseteq> set_btree (Node ts t)"
  by auto

lemma subtrees_in_set:
  "s \<in> set (subtrees ts) \<Longrightarrow> set_btree s \<subseteq> set_btree (Node ts t)"
  by auto


fun bal:: "'a btree \<Rightarrow> bool" where
  "bal Leaf = True" |
  "bal (Node ts t) = ((\<forall>sub \<in> set (subtrees ts). height t = height sub) \<and> (\<forall>sub \<in> set (subtrees ts). bal sub) \<and> bal t)"

lemma bal_all_subtrees_equal: "bal (Node ts t) \<Longrightarrow> (\<forall>s1 \<in> set (subtrees ts). \<forall>s2 \<in> set (subtrees ts). height s1 = height s2)"
  by (metis BTree.bal.simps(2))


find_theorems fold max

lemma fold_max_set: "\<forall>x \<in> set t. x = f \<Longrightarrow> fold max t f = f"
  apply(induction t)
   apply(auto simp add: max_def_raw)
  done

lemma height_bal_tree: "bal (Node ts t) \<Longrightarrow> height (Node ts t) = Suc (height t)"
  by (simp add: fold_max_set)


lemma bal_split: 
  assumes "bal (Node (ls@(sub,sep)#rs) t)"
  shows "bal (Node (ls@rs) t)"
    and "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
proof -
  from assms have
    "bal t"
    "\<forall>sub \<in> set (subtrees (ls@(sub,sep)#rs)). height t = height sub \<and> bal sub"
    using bal.simps(2) by blast+
  moreover have "\<forall>sub \<in> set (subtrees ls) \<union> set (subtrees rs). height t = height sub \<and> bal sub"
    using subtrees_split
    by (simp add: calculation)
  ultimately show
    "bal (Node (ls@rs) t)"
    by auto
  then show "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
    using height_bal_tree assms by metis
qed


lemma bal_split2: 
  assumes "bal (Node (ls@rs) t)"
  shows "bal (Node rs t)"
    and "height (Node rs t) = height (Node (ls@rs) t)"
proof -
  show "bal (Node rs t)"
    using assms by auto
  then show "height (Node rs t) = height (Node (ls@rs) t)"
    using height_bal_tree assms
    by metis
qed

lemma bal_split3:
  assumes "bal (Node (ls@(a,b)#rs) t)"
  shows "bal (Node ls a)"
    and "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
proof -
  from assms have "\<forall>x \<in> set (subtrees ls). height x = height t"
    using subtrees_split by force
  then show "bal (Node ls a)"
    using assms by auto
  moreover have "height a = height t"
    using assms by auto
  ultimately show "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
    using assms height_bal_tree
    by metis
qed


lemma bal_substitute: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height t = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  unfolding bal.simps
  by (metis Un_iff singletonD subtrees_split)

lemma bal_substitute2: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height a = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  using bal_substitute
  by (metis bal.simps(2) in_set_conv_decomp some_child_sub(1))

lemma bal_substitute3: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal (Node (ls@(a,c)#rs) t)"
  unfolding bal.simps
  by (metis subtrees_split)

(*value "nat \<lceil>(5::nat) / 2\<rceil>"*)

(* alt1: following knuths definition to allow for any natural number as order and resolve ambiguity *)
(* alt2: use range [k,2*k] allowing for valid btrees from k=1 onwards *)
fun order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
  "order k Leaf = True" |
  "order k (Node ts t) = (
  (length ts \<ge> k)  \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>sub \<in> set (subtrees ts). order k sub) \<and>
  order k t
)"


(* the invariant for the root of the btree *)
fun root_order where
  "root_order k Leaf = True" |
  "root_order k (Node ts t) = (
  (length ts > 0) \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and>
   order k t
)"


lemma order_impl_root_order: "\<lbrakk>k > 0; order k t\<rbrakk> \<Longrightarrow> root_order k t"
  apply(cases t)
   apply(auto)
  done


value "set_btree_inorder (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"
value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"
  (* a bit weird *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"




(* idea: make sorted_list a sorted_wrt *)
find_theorems sorted_wrt
thm sorted_wrt_append

fun sub_sep_sm where
  "sub_sep_sm (sub_l, sep_l) (sub_r, sep_r) =
  ((sep_l < sep_r) \<and> (\<forall>x \<in> set_btree sub_r. sep_l < x))"

fun sub_sep_cons where
  "sub_sep_cons (sub, sep) = (\<forall>x \<in> set_btree sub. x < sep)"

subsection "sortedness"

fun sorted_alt where
  "sorted_alt Leaf = True" |
  "sorted_alt (Node ts t) = (sorted_wrt sub_sep_sm ts \<and> (\<forall>x \<in> set ts. sub_sep_cons x) \<and> (\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree t. sep < y) \<and> (\<forall>sub \<in> set (subtrees ts). sorted_alt sub) \<and> sorted_alt t)"

value "sorted_less (inorder (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf))"
value "sorted_alt (Node [(Node [(Node [] Leaf, a\<^sub>1)] Leaf, a\<^sub>2)] Leaf)"


lemma sorted_wrt_list_sorted: "sorted_wrt sub_sep_sm xs \<Longrightarrow> sorted_less (seperators xs)"
  by (induction xs) (auto)


lemma sorted_wrt_sorted_left: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> t \<in> set (subtrees xs) \<Longrightarrow> \<forall>x \<in> set_btree t. x > sep"
  by (induction xs) (auto)


lemma sorted_wrt_sorted_left2: "sorted_wrt sub_sep_sm ((sub, sep)#xs) \<Longrightarrow> x \<in> set (seperators xs) \<Longrightarrow> x > sep"
  by (induction xs) (auto)

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
  "(sorted_less (inorder sub) \<and> (\<forall>x \<in> set_btree_inorder sub. x < sep)) = sorted_less((inorder sub) @ [sep])"
  unfolding set_btree_inorder_def using sorted_snoc_iff
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
  assumes "sorted_alt (Node (ls@x#rs) t)"
  shows "sorted_alt (Node (ls@rs) t)"
  unfolding sorted_alt.simps
  apply(safe)
      apply (metis (no_types, lifting) assms list.set_intros(2) sorted_alt.simps(2) sorted_wrt_Cons sorted_wrt_append)
     apply (metis Un_iff assms list.set_intros(2) set_append sorted_alt.simps(2))
  using assms
  by auto

lemma sorted_alt_sorted: "sorted_alt t \<Longrightarrow> sorted_less (inorder t)"
proof(induction t)
  case (Node ts t)
  then have "\<lbrakk>sorted_alt (Node ts t)\<rbrakk> \<Longrightarrow> sorted_less (inorder (Node ts t))"
  proof (induction ts)
    case (Cons a list)
    then have Cons_help: 
      "sorted_wrt sub_sep_sm list" 
      "\<forall>x \<in> set list. sub_sep_cons x"
      "\<forall>sub \<in> set (subtrees list). sorted_alt sub"
      by (simp_all)
    then have "sorted_alt (Node list t)" using Cons
      by simp
    then have Cons_sorted: "sorted_less (inorder (Node list t))"
      using Cons.IH Cons.prems(2) Node.IH(2) by auto

    from Cons obtain sub sep where pair_a: "a = (sub,sep)"
      by (cases a)
    then have "sorted_alt sub" using Node Cons
      by simp
    then have "sorted_less (inorder sub)" using Node Cons pair_a
      by force

    from pair_a have "\<forall>x \<in> set (seperators list). sep < x"
      using sorted_wrt_Cons sorted_wrt_list_sorted Cons_help
      by (metis (no_types, lifting) Cons.prems(1) list.simps(9)  snd_conv sorted_alt.simps(2))
    moreover have "\<forall>t \<in> set (subtrees list). (\<forall>x \<in> set_btree t. sep < x)"
      using pair_a Cons sorted_alt.simps(2) sorted_wrt_sorted_left by metis
    ultimately have "\<forall>x \<in> set_btree (Node list t). sep < x"
      using Cons.prems(1) pair_a by auto
    then have "\<forall>x \<in> set_btree_inorder (Node list t). sep < x"
      by (simp add: set_btree_inorder_set_btree)
    then have sep_sm: "\<forall>x \<in> set (inorder (Node list t)). sep < x"
      unfolding set_btree_inorder_def by auto
    then have "sorted_less (sep # inorder (Node list t))"
      using Cons_sorted sorted_Cons_iff by blast
    moreover have "\<forall>y \<in> set (inorder sub). \<forall>x \<in> set (inorder (Node list t)). y < x"
      using Cons_help sep_sm pair_a Cons
      by (metis comp_apply dual_order.strict_trans list.set_intros(1) set_btree_inorder_def set_btree_inorder_set_btree sorted_alt.simps(2) sub_sep_cons.simps)
    ultimately have "sorted_less (inorder sub @ sep # inorder (Node list t))"
      using sorted_wrt_append[of "(<)" "inorder sub" "sep # inorder (Node list t)"] \<open>sorted_less (inorder (Node list t))\<close>
      by (metis Cons.prems(1) \<open>sorted_less (inorder sub)\<close> list.set_intros(1) pair_a set_btree_inorder_set_btree sorted_alt.simps(2) sorted_mid_iff sorted_pair_list sub_sep_cons.simps)
    then have "sorted_less ((inorder sub @ [sep]) @ inorder (Node list t))"
      by simp
    then have "sorted_less ((\<lambda>(sub, sep). BTree.inorder sub @ [sep]) a @ foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) list) [] @ inorder t)"
      by (simp add: pair_a)
    then have "sorted_less (foldr (@) (map (\<lambda>(sub, sep). BTree.inorder sub @ [sep]) (a#list)) [] @ inorder t)" 
      by simp
    then show ?case by simp
  qed auto
  then show ?case using Node by auto
qed auto

lemma sorted_inorder_subtrees:
  "sorted_less (inorder_list ts) \<Longrightarrow> \<forall>x \<in> set (subtrees ts). sorted_less (inorder x)"
proof(induction ts)
  case (Cons a ts)
  then obtain sub sep where "a = (sub,sep)"
    by (cases a)
  then have "sorted_less (inorder sub)"
    using Cons by (simp add: sorted_wrt_append)
  moreover have "set (subtrees (a#ts)) = set (subtrees ts) \<union> {sub}"
    using \<open>a = (sub,sep)\<close> by auto
  moreover have "sorted_less (inorder_list ts)"
    unfolding inorder_list.simps
    using Cons.prems sorted_wrt_append by fastforce
  ultimately show ?case using Cons
    by auto
qed auto

lemma sorted_inorder_last: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder t)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_subcons: "sorted_less (inorder_list ts) \<Longrightarrow> \<forall>x \<in> set ts. sub_sep_cons x"
proof(induction ts)
  case (Cons a ts)
  then obtain sub sep where "a = (sub,sep)"
    by (cases a)
  then have "sorted_less (inorder sub @ [sep])"
    using Cons by (simp add: sorted_wrt_append)
  then have "sub_sep_cons (sub,sep)"
    unfolding sub_sep_cons.simps
    using set_btree_inorder_set_btree sorted_pair_list
    by fastforce
  moreover have "sorted_less (inorder_list ts)"
    unfolding inorder_list.simps
    using Cons.prems sorted_wrt_append by fastforce
  ultimately show ?case using Cons         
    using \<open>a = (sub,sep)\<close> by auto
qed auto

lemma sorted_inorder_fold: "sorted_less (inorder (Node ts t)) \<Longrightarrow> (\<forall>x \<in> set (inorder_list ts). \<forall>y \<in> set_btree_inorder t. x < y)"
  apply(induction ts)
   apply (simp add: set_btree_inorder_def sorted_Cons_iff sorted_wrt_append)+
  by blast

lemma seperators_subset: "set (seperators xs) \<subseteq> set (inorder_list xs)"
  apply(induction xs)
   apply(auto)
  done

lemma sorted_inorder_seps: "sorted_less (inorder (Node ts t)) \<Longrightarrow> (\<forall>sep \<in> set (seperators ts). \<forall>y \<in> set_btree_inorder t. sep < y)"
  using sorted_inorder_fold seperators_subset by fastforce

lemma sorted_inorder_impl_list: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder_list ts)"
  by (simp add: sorted_wrt_append)


lemma sorted_inorder_subsepsm: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_wrt sub_sep_sm ts"
proof (induction ts)
  case (Cons x list)
  then obtain sub sep where x_pair: "x = (sub, sep)" by (cases x)
  then have list_split: "inorder (Node (x#list) t) = inorder sub @ sep # inorder (Node list t)" unfolding inorder.simps by auto
  then have "sorted_less (inorder (Node list t))" 
    using  Cons.prems sorted_cons
    by (simp add: list_split sorted_wrt_append)
  then have sorted_wrt_rec: "sorted_wrt sub_sep_sm list" using Cons by auto

  from list_split have "\<forall>l \<in> set (inorder (Node list t)). sep < l"
    by (metis Cons.prems sorted_Cons_iff sorted_wrt_append)
  then have "\<forall>l \<in> set_btree_inorder (Node list t). sep < l"
    by (simp add: set_btree_inorder_def)
  then have "\<forall>l \<in> set_btree (Node list t). sep < l"
    by (simp add: set_btree_inorder_set_btree)
  then have sorted_wrt_local: "\<forall>(sub_r, sep_r) \<in> set list. (sep < sep_r \<and> (\<forall>r \<in> set_btree sub_r. sep < r))"
    by (induction list) auto 

  from sorted_wrt_local sorted_wrt_rec show ?case
    unfolding sorted_wrt.simps sub_sep_sm.simps
    using x_pair by auto
qed auto


find_theorems sorted_less inorder

lemma sorted_sorted_alt: "sorted_less (inorder t) \<Longrightarrow> sorted_alt t"
  apply(induction t)
   apply(simp)
  unfolding sorted_alt.simps
  apply (safe)
  using sorted_inorder_subsepsm apply blast
  using sorted_inorder_subcons sorted_inorder_impl_list apply blast
  using sorted_inorder_seps set_btree_inorder_set_btree apply fastforce
  using sorted_inorder_subtrees sorted_inorder_impl_list apply fastforce
  using sorted_inorder_last apply blast
  done

lemma sorted_alt_eq: "sorted_less (inorder t) = sorted_alt t"
  using sorted_alt_sorted sorted_sorted_alt by blast



end