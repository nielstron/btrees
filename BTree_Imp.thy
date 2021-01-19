theory BTree_Imp
  imports
    BTree_Set
    Partially_Filled_Array
    Imperative_Loops
begin

datatype 'a btnode =
  Btnode "('a btnode ref option*'a) pfarray" "'a btnode ref option"

text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option*'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

term arrays_update

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Sollte auch mit deriving gehen *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (ts, t)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
   apply (metis btnode_encode.elims from_nat_to_nat fst_conv snd_conv)
  ..



fun btree_assn :: "nat \<Rightarrow> 'a::heap btree \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "btree_assn k Leaf None = emp" |
  "btree_assn k (Node ts t) (Some a) = 
 (\<exists>\<^sub>A tsi ti tsi'.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * btree_assn k t ti
    * is_pfarray_cap (2*k) tsi' tsi
    * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi'
    )" |
  "btree_assn _ _ _ = false"


find_consts name: while

term split

definition linear_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "linear_split \<equiv> \<lambda> (a,n) p. do {
  
  i \<leftarrow> heap_WHILET 
    (\<lambda>i. if i<n then do {
      (_,s) \<leftarrow> Array.nth a i;
      return (s<p)
    } else return False) 
    (\<lambda>i. return (i+1)) 
    0;
       
  return i
}"



lemma linear_split_rule: "
< is_pfarray_cap c xs (a,n) * true>
 linear_split (a,n) p
 <\<lambda>i. is_pfarray_cap c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p)) >\<^sub>t"
  unfolding linear_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>i. n - i)"
      and I = "\<lambda>i. is_pfarray_cap c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p))"
      and b = "\<lambda>i. i<n \<and> snd (xs!i) < p"
      ]
  thm R

  apply (sep_auto  decon: R simp: less_Suc_eq is_pfarray_cap_def) []
      apply (metis nth_take snd_eqD)
     apply (metis nth_take snd_eqD)
    apply (sep_auto simp: is_pfarray_cap_def less_Suc_eq)+
     apply (metis dual_order.strict_trans nth_take)
    apply (metis nth_take)
  using diff_less_mono2 apply blast
  apply(sep_auto simp: is_pfarray_cap_def)
  done


definition bin'_split :: "'b::{heap,linorder} array_list \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin'_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      s \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm sorted_wrt_nth_less

(* alternative: replace (\<forall>j<l. xs!j < p) by (l > 0 \<longrightarrow> xs!(l-1) < p)*)
lemma bin'_split_rule: "
sorted_less xs \<Longrightarrow>
< is_pfarray_cap c xs (a,n) * true>
 bin'_split (a,n) p
 <\<lambda>l. is_pfarray_cap c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p)) >\<^sub>t"
  unfolding bin'_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfarray_cap c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (h<n \<longrightarrow> xs!h\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfarray_cap c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p)) * true"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfarray_cap_def) []
  subgoal for l' aa l'a aaa ba j
  proof -
    assume 0: "n \<le> length l'a"
    assume a: "l'a ! ((aa + n) div 2) < p"
    moreover assume "aa < n"
    ultimately have b: "((aa+n)div 2) < n"
      by linarith
    then have "(take n l'a) ! ((aa + n) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+n)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and ?xs="(take n l'a)" and ?j="((aa + n) div 2)"]
      a b "0" by auto
    moreover fix j assume "j < (aa+n) div 2"
    ultimately show "l'a ! j < p" using "0" b
      using \<open>take n l'a ! ((aa + n) div 2) < p\<close> dual_order.strict_trans by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "n \<le> length l'a"
    assume t1: "aa < b"
    assume a: "l'a ! ((aa + b) div 2) < p"
    moreover assume "b \<le> n"
    ultimately have b: "((aa+b)div 2) < n" using t1
      by linarith
    then have "(take n l'a) ! ((aa + b) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+b)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and ?xs="(take n l'a)" and ?j="((aa + b) div 2)"]
      a b t0 by auto
    moreover fix j assume "j < (aa+b) div 2"
    ultimately show "l'a ! j < p" using t0 b
      using \<open>take n l'a ! ((aa + b) div 2) < p\<close> dual_order.strict_trans by auto
  qed
     apply sep_auto
      apply (metis le_less nth_take)
     apply (metis le_less nth_take)
  apply sep_auto
  subgoal for l' aa l'a aaa ba j
  proof -
    assume t0: "aa < n"
    assume t1: " n \<le> length l'a"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + n) div 2"
    have "(aa+n) div 2 < n" using t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using t0 sorted_wrt_nth_less[where ?xs="take n l'a" and ?j="((aa + n) div 2)"]
       t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + n) div 2 < n\<close> t5 by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "aa < b"
    assume t1: " n \<le> length l'a"
    assume t3: "b \<le> n"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + b) div 2"
    have "(aa+b) div 2 < n" using t3 t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using t0 sorted_wrt_nth_less[where ?xs="take n l'a" and ?j="((aa + b) div 2)"]
       t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + b) div 2 < n\<close> t5 by auto
  qed
    apply (metis nth_take order_mono_setup.refl)
   apply sep_auto
  apply (sep_auto simp add: is_pfarray_cap_def)
  done


definition bin_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      (_,s) \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm nth_take

lemma nth_take_eq: "take n ls = take n ls' \<Longrightarrow> i < n \<Longrightarrow> ls!i = ls'!i"
  by (metis nth_take)

lemma map_snd_sorted_less: "\<lbrakk>sorted_less (map snd xs); i < j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) < snd (xs ! j)"
  by (metis (mono_tags, hide_lams) length_map less_trans nth_map sorted_wrt_iff_nth_less)

lemma map_snd_sorted_lesseq: "\<lbrakk>sorted_less (map snd xs); i \<le> j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) \<le> snd (xs ! j)"
  by (metis eq_iff less_imp_le map_snd_sorted_less order.not_eq_order_implies_strict)

lemma bin_split_rule: "
sorted_less (map snd xs) \<Longrightarrow>
< is_pfarray_cap c xs (a,n) * true>
 bin_split (a,n) p
 <\<lambda>l. is_pfarray_cap c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd(xs!j) < p) \<and> (l<n \<longrightarrow> snd(xs!l)\<ge>p)) >\<^sub>t"
(* this works in principle, as demonstrated above *)
    unfolding bin_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfarray_cap c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (h<n \<longrightarrow> snd (xs!h)\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfarray_cap c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (l<n \<longrightarrow> snd (xs!l)\<ge>p)) * true"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfarray_cap_def) []
  
      apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
     apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
    apply (sep_auto dest!: sndI )
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_lesseq[of "take n ls'" j "(i + n) div 2"] 
    less_mult_imp_div_less apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_lesseq[of "take n ls'" j' "(i + j) div 2"] 
    less_mult_imp_div_less apply(auto)[]
    done
    apply sep_auto
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_less[of "take n ls'" j "(i + n) div 2"] 
      less_mult_imp_div_less
     apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_less[of "take n ls'" j' "(i + j) div 2"] 
      less_mult_imp_div_less
     apply(auto)[]
    done
    apply (metis le_less nth_take_eq)
   apply sep_auto
  apply (sep_auto simp add: is_pfarray_cap_def)
done
    
     

lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  by auto


definition "abs_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"

interpretation btree_abs_search: split abs_split
  apply unfold_locales
  unfolding abs_split_def
    apply (auto simp: split: list.splits)
  subgoal
    by (metis (no_types, lifting) append_is_Nil_conv append_self_conv case_prodD dropWhile_append1 list.simps(3) takeWhile_dropWhile_id takeWhile_eq_all_conv takeWhile_idem takeWhile_tail)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done

definition "split_relation xs \<equiv> \<lambda>(as,bs) i. i \<le> length xs \<and> as = take i xs \<and> bs = drop i xs"

lemma split_relation_alt: 
  "split_relation as (ls,rs) i = (as = ls@rs \<and> i = length ls)"
  by (auto simp add: split_relation_def)



lemma split_relation_map: "split_relation as (ls,rs) i \<Longrightarrow> split_relation (map f as) (map f ls, map f rs) i"
  apply(induction as arbitrary: ls rs i)
   apply(auto simp add: split_relation_def take_map drop_Cons')
   apply (metis list.simps(9) take_map)
  apply (simp add: drop_map)
  done

lemma split_relation_access: "\<lbrakk>split_relation as (ls,rs) i; rs = r#rrs\<rbrakk> \<Longrightarrow> as!i = r"
  by (simp add: split_relation_alt)



lemma index_to_elem_all: "(\<forall>j<length xs. P (xs!j)) = (\<forall>x \<in> set xs. P x)"
  by (simp add: all_set_conv_nth)

lemma index_to_elem: "n < length xs \<Longrightarrow> (\<forall>j<n. P (xs!j)) = (\<forall>x \<in> set (take n xs). P x)"
  by (simp add: all_set_conv_nth)

lemma abs_split_full: "\<forall>(_,s) \<in> set xs. s < p \<Longrightarrow> abs_split xs p = (xs,[])"
  by (simp add: abs_split_def)

lemma abs_split_split:
  assumes "n < length xs" 
    and "(\<forall>(_,s) \<in> set (take n xs). s < p)"
    and " (case (xs!n) of (_,s) \<Rightarrow> \<not>(s < p))"
  shows "abs_split xs p = (take n xs, drop n xs)"
  using assms  apply (auto simp add: abs_split_def)
   apply (metis (mono_tags, lifting) id_take_nth_drop old.prod.case takeWhile_eq_all_conv takeWhile_tail)
  by (metis (no_types, lifting) Cons_nth_drop_Suc case_prod_conv dropWhile.simps(2) dropWhile_append2 id_take_nth_drop)



lemma split_relation_length: "split_relation xs (ls,rs) (length xs) = (ls = xs \<and> rs = [])"
  by (simp add: split_relation_def)

thm index_to_elem_all[of ts "\<lambda>x. snd x < p"]

lemma list_assn_all: "h \<Turnstile> (list_assn (\<up>\<circ>\<circ>P) xs ys) \<Longrightarrow> (\<forall>i<length xs. P (xs!i) (ys!i))"
  apply(induction "\<up>\<circ>\<circ>P" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj)
  done

(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct "(A \<times>\<^sub>a B)" xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done

find_theorems Id


(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn (xs::'a list) ys \<Longrightarrow> xs = ys"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done


lemma snd_map_help:
  "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
  "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto

(* new, added for the "interesting part" *)

lemma abs_split_split_map:
  assumes "n < length xs" 
    and "\<forall>i < n. snd(xs!i) < p"
    and " snd (xs!n) \<ge> (p::'a::linorder)"
  shows "abs_split xs p = (take n xs, drop n xs)"
  using assms  apply(auto dest!: abs_split_split)
  by (metis (no_types, lifting) assms(1) in_set_conv_nth length_take less_imp_le min.absorb2 nth_take snd_conv)

find_theorems takeWhile

lemma abs_split_eq_taken_dropn: "abs_split as x = (take (length (takeWhile (\<lambda>(uu, s). s < x) as)) as, drop (length (takeWhile (\<lambda>(uu, s). s < x) as)) as)"
  unfolding abs_split_def
  using dropWhile_eq_drop takeWhile_eq_take
  by auto


lemma length_map_takeWhile_eq: "map f as = map f' bs \<Longrightarrow> 
      length (takeWhile f as) = length (takeWhile f' bs)"
proof -
  assume map_eq: "map f as = map f' bs"
  then have "length as = length bs"
    using map_eq_imp_length_eq by blast
  then show ?thesis
    using map_eq
  proof(induction as bs rule: list_induct2)
    case (Cons x xs y ys)
    then show ?case
    proof (cases "f x")
      case True
      then show ?thesis
        using Cons.IH Cons.prems by auto
    next
      case False
      then show ?thesis
        using Cons.prems by auto
    qed
  qed auto
qed

lemma map_snd_lambda: "map f as = map f' bs \<Longrightarrow> map (P \<circ> f) as = map (P \<circ> f') bs"
  by (metis map_map)
thm map_map

lemma snd_simp: "snd = (\<lambda>(uu,s). s)"
  by auto

lemma concat_snd: "P \<circ> (\<lambda>(uu,s). s) = (\<lambda>(uu,s). P s)"
  by auto

lemma length_takeWhile_eq_snd: "map snd as = map snd bs \<Longrightarrow>
   (length (takeWhile (\<lambda>(uu, s). s < x) as)) = (length (takeWhile (\<lambda>(uu, s). s < x) bs ))"
proof -
  assume "map snd as = map snd bs"
  then have "map (\<lambda>(uu,s). s) as = map (\<lambda>(uu,s). s) bs"
    by (simp add: snd_simp concat_snd)
  then have "map (\<lambda>y. y < x) (map (\<lambda>(uu,s). s) as) = map (\<lambda>y. y < x) (map (\<lambda>(uu,s). s) bs)"
    by simp
  then have "map (\<lambda>(uu,s). s < x) as = map (\<lambda>(uu,s). s < x) bs"
    by (simp add: concat_snd)
  then show ?thesis
    using length_map_takeWhile_eq[of "\<lambda>(uu,s). s < x" as "\<lambda>(uu,s). s < x" bs]
    by simp
qed


lemma split_rule_abs_split: 
  assumes split_rule: "\<And> c xs a n p. P c xs a n p \<Longrightarrow>  <is_pfarray_cap c xs (a, n) *
 true> split_fun (a, n) (p::'a::{heap,linorder}) <\<lambda>r. is_pfarray_cap c xs (a, n) *
                 \<up> (r \<le> n \<and>
                    (\<forall>j<r. snd (xs ! j) < p) \<and> (r < n \<longrightarrow> p \<le> snd (xs ! r)))>\<^sub>t"
  shows
"P c tsi a n p \<Longrightarrow> <
    is_pfarray_cap c tsi (a,n)
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi
  * true> 
    split_fun (a,n) p 
  <\<lambda>i. 
    is_pfarray_cap c tsi (a,n)
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>(split_relation ts (abs_split ts p) i)>\<^sub>t"
  thm split_rule
  apply (sep_auto heap: split_rule dest!: mod_starD id_assn_list
      simp add: list_assn_prod_map split_ismeq)
(* the interesting path: finding the correct rules for automatic rewriting:
    apply(auto dest!: hoare_triple_preI list_assn_len
          simp add: is_pfarray_cap_def split_relation_def min.absorb1 min.absorb2 )[]
  subgoal for x _ _ _ _ as bs ls
    by (smt abs_split_split_map le_antisym le_trans length_map less_imp_le_nat linorder_neqE_nat nth_take order_mono_setup.refl prod.inject snd_map_help(1))
  subgoal for x _ _ _ _ as bs ls
    by (metis \<open>\<And>x ls bs be bb as ae ab. \<lbrakk>in_range (ab, bb); seperators ts = seperators (take (length ts) ls); x < length ts; \<forall>j<x. snd (ls ! j) < p; p \<le> snd (ls ! x); (as, bs) = abs_split ts p; (ae, be) \<Turnstile> a \<mapsto>\<^sub>a ls; c = length ls; length ts \<le> length ls; tsi = take (length ts) ls; n = length ts\<rbrakk> \<Longrightarrow> as = take x ts\<close> abs_split_eq_taken_dropn length_take min_simps(2) snd_conv takeWhile_eq_take)
    apply(auto dest!: hoare_triple_preI list_assn_len
          simp add: is_pfarray_cap_def split_relation_def min.absorb1 min.absorb2 )[]
stops here...
*)
      apply(simp_all add: is_pfarray_cap_def)
    apply(auto)
proof -

  fix h l' assume heap_init:
    "h \<Turnstile> a \<mapsto>\<^sub>a l'"
    "map snd ts = (map snd (take n l'))"
    "n \<le> length l'"


  show full_thm: "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
  proof -
    assume sm_list: "\<forall>j<n. snd (l' ! j) < p"
    then have "\<forall>j < length (map snd (take n l')). ((map snd (take n l'))!j) < p"
      by simp
    then have "\<forall>j<length (map snd ts). ((map snd ts)!j) < p"
      using heap_init by simp
    then have "\<forall>(_,s) \<in> set ts. s < p"
      by (metis case_prod_unfold in_set_conv_nth length_map nth_map)
    then have "abs_split ts p = (ts, [])"
      using abs_split_full[of ts p] by simp
    then show "split_relation ts (abs_split ts p) n"
      using split_relation_length
      by (metis heap_init(2) heap_init(3) length_map length_take min.absorb2)

  qed
  then show "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (take n l' ! n) \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
    by simp

  show part_thm: "\<And>x. x < n \<Longrightarrow>
       \<forall>j<x. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (l' ! x) \<Longrightarrow> split_relation ts (abs_split ts p) x"
  proof -
    fix x assume x_sm_len: "x < n"
    moreover assume sm_list: "\<forall>j<x. snd (l' ! j) < p"
    ultimately have "\<forall>j<x. ((map snd l') ! j) < p"
      using heap_init
      by auto
    then have "\<forall>j<x. ((map snd ts)!j) < p"
      using heap_init  x_sm_len
      by auto
    moreover have x_sm_len_ts: "x < n"
      using heap_init x_sm_len by auto
    ultimately have "\<forall>(_,x) \<in> set (take x ts). x < p"
      by (auto simp add: in_set_conv_nth  min.absorb2)+
    moreover assume "p \<le> snd (l' ! x)"
    then have "case l'!x of (_,s) \<Rightarrow> \<not>(s < p)"
      by (simp add: case_prod_unfold)
    then have "case ts!x of (_,s) \<Rightarrow> \<not>(s < p)"
      using heap_init x_sm_len x_sm_len_ts
      by (metis (mono_tags, lifting) case_prod_unfold length_map length_take min.absorb2 nth_take snd_map_help(2))
    ultimately have "abs_split ts p = (take x ts, drop x ts)"
      using x_sm_len_ts abs_split_split[of x ts p] heap_init
      by (metis length_map length_take min.absorb2)
    then show "split_relation ts (abs_split ts p) x"
      using x_sm_len_ts 
      by (metis append_take_drop_id heap_init(2) heap_init(3) length_map length_take less_imp_le_nat min.absorb2 split_relation_alt)
  qed
qed


lemma linear_split_imp_abs_split[sep_heap_rules]: "<
    is_pfarray_cap c tsi (a,n)
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi
  * true> 
    linear_split (a,n) p 
  <\<lambda>i. 
    is_pfarray_cap c tsi (a,n)
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>(split_relation ts (abs_split ts p) i)>\<^sub>t"
  thm  split_rule_abs_split[OF linear_split_rule]
  by (sep_auto heap: split_rule_abs_split[OF linear_split_rule])

(* since we have shown the abstract behavior for sorted lists
the proof from above needs nearly no amendmend *)
lemma bin_split_imp_abs_split[sep_heap_rules]: "
sorted_less (map snd ts) \<Longrightarrow> <
    is_pfarray_cap c tsi (a,n)
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi
  * true> 
    bin_split (a,n) p 
  <\<lambda>i. 
    is_pfarray_cap c tsi (a,n)
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>(split_relation ts (abs_split ts p) i)>\<^sub>t"
  apply(rule hoare_triple_preI)
  thm split_rule_abs_split[OF bin_split_rule]
  apply (sep_auto heap: split_rule_abs_split[OF bin_split_rule])
   apply(auto dest!: mod_starD id_assn_list simp add: list_assn_prod_map)
  done

partial_function (heap) isin :: "('a::{heap,linorder}) btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin p x = 
  (case p of 
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> linear_split (kvs node) x;
       tsl \<leftarrow> pfa_length (kvs node);
       if i < tsl then do {
         s \<leftarrow> pfa_get (kvs node) i;
         let (sub,sep) = s in
         if x = sep then
           return True
         else
           isin sub x
       } else
           isin (last node) x
    }
)"


lemma P_imp_Q_implies_P: "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by simp

lemma  "<btree_assn k t ti * true> isin ti x <\<lambda>r. btree_assn k t ti * \<up>(btree_abs_search.isin t x = r)>\<^sub>t"
proof(induction t x arbitrary: ti rule: btree_abs_search.isin.induct)
  case (1 x)
  then show ?case
    apply(subst isin.simps)
    apply (cases ti)
     apply (auto simp add: return_cons_rule)
    done
next
  case (2 ts t x)
  then obtain ls rs where list_split[simp]: "abs_split ts x = (ls,rs)"
    by (cases "abs_split ts x")
  then show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin.simps)
      apply(sep_auto heap: linear_split_imp_abs_split)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
       apply(rule hoare_triple_preI)
       apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      apply(sep_auto heap: "2.IH"(1)[of ls "[]"])
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
    show ?thesis
    proof (cases "sep = x")
      (* NOTE: no induction required here, only vacuous counter cases generated *)
      case [simp]: True
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin.simps)
        apply(sep_auto heap: linear_split_imp_abs_split)
         apply(rule hoare_triple_preI)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
        done
    next
      case [simp]: False
      show ?thesis
        apply(simp split: list.splits prod.splits)
        apply safe
        using False apply simp
        apply(subst isin.simps)
        apply(sep_auto heap: linear_split_imp_abs_split)
          (*eliminate vacuous case*)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!:  mod_starD list_assn_len)[]
          (* simplify towards induction step *)
        apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]

(* NOTE show that z = (suba, sepa) *)
        apply(rule norm_pre_ex_rule)+
        apply(rule hoare_triple_preI)
        subgoal for p tsi n ti xsi suba sepa zs1 z zs2 _
          apply(subgoal_tac "z = (suba, sepa)", simp)
          apply(sep_auto heap:"2.IH"(2)[of ls rs h rrs sub sep])
          using list_split Cons h_split apply simp_all
            (* proof that previous assumptions hold later *)
          apply(rule P_imp_Q_implies_P)
          apply(rule ent_ex_postI[where ?x="(tsi,n)"])
          apply(rule ent_ex_postI[where ?x="ti"])
          apply(rule ent_ex_postI[where ?x="(zs1 @ (suba, sepa) # zs2)"])
          apply(rule ent_ex_postI[where ?x="zs1"])
          apply(rule ent_ex_postI[where ?x="z"])
          apply(rule ent_ex_postI[where ?x="zs2"])
          apply sep_auto
            (* prove subgoal_tac assumption *)
          apply (metis (no_types, lifting) list_assn_aux_ineq_len list_assn_len nth_append_length star_false_left star_false_right)
          done
            (* eliminate last vacuous case *)
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
        done
    qed
  qed
qed



definition split_half :: "('a::heap \<times> 'b::{heap}) pfarray \<Rightarrow> nat Heap"
  where
    "split_half a \<equiv> do {
  l \<leftarrow> pfa_length a;
  return (l div 2)
}"

lemma split_half_rule[sep_heap_rules]: "<
    is_pfarray_cap c tsi a
  * list_assn R ts tsi> 
    split_half a
  <\<lambda>i. 
      is_pfarray_cap c tsi a
    * list_assn R ts tsi
    * \<up>(i = length ts div 2 \<and>  split_relation ts (BTree_Set.split_half ts) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done

datatype 'a btupi = 
  T\<^sub>i "'a btnode ref option" |
  Up\<^sub>i "'a btnode ref option" "'a" "'a btnode ref option"

fun btupi_assn where
  "btupi_assn k (btree_abs_search.T\<^sub>i l) (T\<^sub>i li) =
   btree_assn k l li" |
  "btupi_assn k (btree_abs_search.Up\<^sub>i l a r) (Up\<^sub>i li ai ri) =
   btree_assn k l li * id_assn a ai * btree_assn k r ri" |
  "btupi_assn _ _ _ = false"



definition node\<^sub>i :: "nat \<Rightarrow> (('a::{default,heap}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap" where
  "node\<^sub>i k a ti \<equiv> do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      l \<leftarrow> ref (Btnode a' ti);
      return (T\<^sub>i (Some l))
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('a btnode ref option \<times> 'a) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a i;
      b' \<leftarrow> pfa_drop a (i+1) b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        l \<leftarrow> ref (Btnode a'' sub);
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i (Some l) sep (Some r))
      }
    }
}"
term Array.upd

thm drop_eq_ConsD

find_theorems "<emp>_<_>"




lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
  shows "<is_pfarray_cap c tsi (a,n) * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi * btree_assn k t ti * true>
  node\<^sub>i k (a,n) ti
  <\<lambda>r. btupi_assn k (btree_abs_search.node\<^sub>i k ts t) r >\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
    apply(sep_auto simp add: is_pfarray_cap_def)[]
    using c_cap apply(sep_auto simp add: is_pfarray_cap_def)[]
    apply(sep_auto  dest!: mod_starD list_assn_len)[]
    using True apply(sep_auto dest!: mod_starD list_assn_len)
    done
next
  case [simp]: False
  then obtain ls sub sep rs where
    split_half_eq: "BTree_Set.split_half ts = (ls,(sub,sep)#rs)"
    using node\<^sub>i_cases by blast
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
    apply(sep_auto simp add:  split_relation_alt split_relation_length is_pfarray_cap_def dest!: mod_starD list_assn_len)

    using False apply(sep_auto simp add: split_relation_alt )
    using False  apply(sep_auto simp add: is_pfarray_cap_def)[]
    apply(sep_auto)[]
    apply(sep_auto simp add: is_pfarray_cap_def split_relation_alt)[]
    using c_cap apply(sep_auto simp add: is_pfarray_cap_def)[]
    apply(sep_auto)[]
    using c_cap apply(sep_auto simp add: is_pfarray_cap_def)[]
    using c_cap apply(simp)
    apply(vcg)
    apply(simp)
    apply(rule impI)
    subgoal for _ _ _ _ _ _ rsa subi ba rn lsi al ar _
      thm ent_ex_postI
      thm ent_ex_postI[where ?x="take (length tsi div 2) tsi"]
        (* instantiate right hand side *)
      apply(rule ent_ex_postI[where ?x="(rsa,rn)"])
      apply(rule ent_ex_postI[where ?x="ti"])
      apply(rule ent_ex_postI[where ?x="(drop (Suc (length tsi div 2)) tsi)"])
      apply(rule ent_ex_postI[where ?x="lsi"])
      apply(rule ent_ex_postI[where ?x="subi"])
      apply(rule ent_ex_postI[where ?x="take (length tsi div 2) tsi"])
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply(simp add: split_relation_alt)
      apply(subgoal_tac "tsi =
            take (length tsi div 2) tsi @ (subi, ba) # drop (Suc (length tsi div 2)) tsi")
      apply(rule back_subst[where a="list_assn (btree_assn k \<times>\<^sub>a id_assn) ts (take (length tsi div 2) tsi @ (subi, ba) # (drop (Suc (length tsi div 2)) tsi))" and b="list_assn (btree_assn k \<times>\<^sub>a id_assn) ts tsi"])
      apply(rule back_subst[where a="list_assn (btree_assn k \<times>\<^sub>a id_assn) (take (length tsi div 2) ts @ (sub, sep) # rs)" and b="list_assn (btree_assn k \<times>\<^sub>a id_assn) ts"])
      apply(subst list_assn_aux_append_Cons)
      apply sep_auto
      apply sep_auto
      apply simp
      apply simp
      apply(rule back_subst[where a="tsi ! (length tsi div 2)" and b="(subi, ba)"])
      apply(rule id_take_nth_drop)
      apply simp
      apply simp
      done
    done
qed

term Array.set

partial_function (heap) ins :: "nat \<Rightarrow> 'a \<Rightarrow> ('a::{heap,linorder,default}) btnode ref option \<Rightarrow> 'a btupi Heap"
  where
    "ins k x p = (case p of
  None \<Rightarrow> 
    return (Up\<^sub>i None x None) |
  (Some a) \<Rightarrow> do {
    node \<leftarrow> !a;
    i \<leftarrow> linear_split (kvs node) x;
    tsl \<leftarrow> pfa_length (kvs node);
    if i < tsl then do {
      s \<leftarrow> pfa_get (kvs node) i;
      let (sub,sep) = s in
      if sep = x then
        return (T\<^sub>i p)
      else do {
        r \<leftarrow> ins k x sub;
        case r of 
          (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set (kvs node) i (lp,sep);
            return (T\<^sub>i p)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            kvs' \<leftarrow> pfa_set (kvs node) i (rp,sep);
            kvs'' \<leftarrow> pfa_insert_grow kvs' i (lp,x');
            node\<^sub>i k kvs'' (last node)
          }
        }
      }
    else do {
      r \<leftarrow> ins k x (last node);
      case r of 
        (T\<^sub>i lp) \<Rightarrow> do {
          a := (Btnode (kvs node) lp);
          return (T\<^sub>i p)
        } |
        (Up\<^sub>i lp x' rp) \<Rightarrow> do {
          kvs' \<leftarrow> pfa_append_grow' (kvs node) (lp,x');
          node\<^sub>i k kvs' rp
        }
    }
  }
)"

declare ins.simps[code]
export_code ins checking SML Scala

declare btree_abs_search.node\<^sub>i.simps[simp del]


lemma node\<^sub>i_rule_app: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1\<rbrakk> \<Longrightarrow>
<is_pfarray_cap c (tsi' @ [(li, ai)]) (aa, al) *
   list_assn (btree_assn k \<times>\<^sub>a id_assn) ls tsi' *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri *
   true> node\<^sub>i k (aa, al) ri
 <btupi_assn k (btree_abs_search.node\<^sub>i k (ls @ [(l, a)]) r)>\<^sub>t"
proof -
  note node\<^sub>i_rule[of k c "(tsi' @ [(li, ai)])" aa al "(ls @ [(l, a)])" r ri]
  moreover assume "2*k \<le> c" "c \<le> 4*k+1"
  ultimately show ?thesis
    by (simp add: mult.left_assoc)
qed

lemma node\<^sub>i_rule_ins2: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfarray_cap c (lsi @ (li, ai) # (ri,a'i) # rsi) (aa, al) *
   list_assn (btree_assn k \<times>\<^sub>a id_assn) ls lsi *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri *
   id_assn a' a'i *
   list_assn (btree_assn k \<times>\<^sub>a id_assn) rs rsi *
   btree_assn k t ti *
   true> node\<^sub>i k (aa, al)
          ti <btupi_assn k (btree_abs_search.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (li, ai) # (ri,a'i) # rsi)" aa al "(ls @ (l, a) # (r,a') # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed


lemma ins_rule:
  shows "<btree_assn k t ti * true>
  ins k x ti
  <\<lambda>r. btupi_assn k (btree_abs_search.ins k x t) r>\<^sub>t"
proof (induction k x t arbitrary: ti rule: btree_abs_search.ins.induct)
  case (1 k x)
  then show ?case
    apply(subst ins.simps)
    apply (sep_auto simp add: pure_app_eq)
    done
next
  case (2 k x ts t)
  then obtain ls rrs where list_split: "abs_split ts x = (ls,rrs)"
    by (cases "abs_split ts x")
  then show ?case
  proof (cases rrs)
    case Nil
    then show ?thesis
    proof (cases "btree_abs_search.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto heap: linear_split_imp_abs_split)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa xc sub sep
          apply(rule hoare_triple_preI)
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split T\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for xi
            apply(cases xi)
            apply sep_auto
            apply sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto heap: linear_split_imp_abs_split)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)                 
        subgoal for p tsil tsin tti tsi' xb xaa xc sub sep
          using Nil list_split 
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split Up\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for xi
            apply(cases xi)
            apply sep_auto
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then show ?thesis
    proof(cases "x = sep")
      case True
      show ?thesis
        apply(subst ins.simps)
        apply(sep_auto heap: linear_split_imp_abs_split)
        subgoal for p tsil tsin tti tsi j subi
          using Cons list_split a_split True
          by sep_auto
        subgoal for p tsil tsin tti tsi j _ _ subi sepi
          apply(rule hoare_triple_preI)
          using Cons list_split a_split True
          apply(subgoal_tac "sepi = sep")
          apply (sep_auto simp add: split_relation_alt)
          apply(sep_auto simp add: list_assn_prod_map dest!: mod_starD id_assn_list)
          by (metis length_map snd_conv snd_map_help(2) split_relation_access)
        subgoal for p tsil tsin tti tsi j
          apply(rule hoare_triple_preI)
          using Cons list_split
          by (sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
        done
    next
      case False
      then show ?thesis
      proof (cases "btree_abs_search.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
          apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
            apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply (cases a, simp)
            apply(subgoal_tac "subi = suba", simp)
            using list_split a_split T\<^sub>i False
            apply (vcg heap: 2)
            apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
            apply vcg
            apply simp
            apply vcg
            apply simp
            subgoal for a'i q r
              apply(rule impI)
              apply(simp add: list_assn_append_Cons_left)
              apply(rule ent_ex_postI[where ?x="(tsil,tsin)"])
              apply(rule ent_ex_postI[where ?x="ti"])
              apply(rule ent_ex_postI[where ?x="(zs1 @ (a'i, sepi) # zs2)"])
              apply(rule ent_ex_postI[where ?x="zs1"])
              apply(rule ent_ex_postI[where ?x="(a'i,sep)"])
              apply(rule ent_ex_postI[where ?x="zs2"])
              apply sep_auto
              apply (simp add: pure_app_eq)
              apply(sep_auto dest!:  mod_starD list_assn_len)[]
              done
            apply (metis Imperative_Loops.list_assn_aux_ineq_len Pair_inject list_assn_len nth_append_length star_false_left star_false_right)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
          apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
            apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply(subgoal_tac "subi = suba", simp)
            thm 2(2)[of ls rrs a rs sub sep]
            using list_split a_split Cons Up\<^sub>i False
            apply (sep_auto heap: 2(2))
            apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
            apply vcg
            apply simp
            subgoal for x21 x22 x23 u
              apply (cases u,simp)
              thm pfa_insert_grow_rule[where ?l="((zs1 @ (suba, sepi) # zs2)[length ls := (x23, sepa)])"]
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              apply (simp add: is_pfarray_cap_def)[]
              apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
              apply(auto split: prod.splits  dest!: mod_starD list_assn_len)[]

              apply (vcg heap: node\<^sub>i_rule_ins2)
              apply simp
              apply simp
              apply simp
              apply sep_auto
              done
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      qed
    qed
  qed
qed

declare btree_abs_search.ins.simps[simp del]

(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a btree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)" 

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert :: "nat \<Rightarrow> ('a::{heap,default,linorder}) \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option Heap" where
"insert \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return (Some t')
      }
}"

lemma insert_rule:
  assumes "k > 0"
  shows "<btree_assn k t ti * true>
  insert k x ti
  <\<lambda>r. btree_assn k (btree_abs_search.insert k x t) r>\<^sub>t"
  unfolding insert_def
  apply(cases "btree_abs_search.ins k x t")
   apply(sep_auto split!: btupi.splits heap: ins_rule)
  using assms
  apply(vcg heap: ins_rule)
  apply(simp split!: btupi.splits)
  apply(vcg)
   apply simp
  apply simp
  apply vcg
  apply auto[]
  subgoal for x21 x22 x23 x21a x22a x23a a b xa
    apply(rule ent_ex_postI[where ?x="(a,b)"])
    apply(rule ent_ex_postI[where ?x="x23a"])
    apply(rule ent_ex_postI[where ?x="[(x21a, x22a)]"])
    apply sep_auto
    done
  done




(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)
definition rebalance_middle_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> nat \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
"rebalance_middle_tree \<equiv> \<lambda> k tsi i r_ti. (
  case r_ti of
  None \<Rightarrow> do {
    return (Btnode tsi r_ti)
  } |
  Some p_t \<Rightarrow> do {
      ti \<leftarrow> !p_t;
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      case r_sub of (Some p_sub) \<Rightarrow>  do {
      sub \<leftarrow> !p_sub;
      l_sub \<leftarrow> pfa_length (kvs sub);
      l_ti \<leftarrow> pfa_length (kvs ti);
      if l_sub \<ge> k \<and> l_ti \<ge> l_ti then do {
        return (Btnode tsi r_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if l_tsi = (i+1) then do {
          mts' \<leftarrow> pfa_append_extend_grow (kvs sub) ((last sub),sep) (kvs ti);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last ti);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> return (Btnode tsi u) |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_append tsi (l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          case r_rsub of Some p_rsub \<Rightarrow> do {
            rsub \<leftarrow> !p_rsub;
            mts' \<leftarrow> pfa_append_extend_grow (kvs sub) (last sub,sep) (kvs rsub);
            res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last rsub);
            case res_node\<^sub>i of
             T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi (i+1) (u,rsep);              
              tsi'' \<leftarrow> pfa_delete tsi' i;
              return (Btnode tsi'' r_ti)
            } |
             Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (l,a);
              tsi'' \<leftarrow> pfa_set tsi' (i+1) (r,rsep);
              return (Btnode tsi'' r_ti)
            }
          }
        }
      }
  }
})
"

definition rebalance_last_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
"rebalance_last_tree \<equiv> \<lambda>k tsi ti. do {
   l_tsi \<leftarrow> pfa_length tsi;
   rebalance_middle_tree k tsi (l_tsi-1) ti
}"

partial_function (heap) split_max ::"nat \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> ('a btnode ref option \<times> 'a) Heap"
  where
"split_max k r_t = (case r_t of Some p_t \<Rightarrow> do {
   t \<leftarrow> !p_t;
   (case t of Btnode tsi r_ti \<Rightarrow>
     case r_ti of None \<Rightarrow> do {
      (sub,sep) \<leftarrow> pfa_last tsi;
      tsi' \<leftarrow> pfa_butlast tsi;
      p_t := Btnode tsi' sub;
      return (Some p_t, sep)
  } |
    _ \<Rightarrow> do {
      (sub,sep) \<leftarrow> split_max k r_ti;
      p_t' \<leftarrow> rebalance_last_tree k tsi sub;
      p_t := p_t';
      return (Some p_t, sep)
  })
})
"

partial_function (heap) isin' :: "('a::{heap,linorder}) btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin' p x = 
  (case p of 
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> bin_split (kvs node) x;
       tsl \<leftarrow> pfa_length (kvs node);
       if i < tsl then do {
         s \<leftarrow> pfa_get (kvs node) i;
         let (sub,sep) = s in
         if x = sep then
           return True
         else
           isin' sub x
       } else
           isin (last node) x
    }
)"


lemma  "sorted_less (inorder t) \<Longrightarrow> <btree_assn k t ti * true> isin ti x <\<lambda>r. btree_assn k t ti * \<up>(btree_abs_search.isin t x = r)>\<^sub>t"
proof(induction t x arbitrary: ti rule: btree_abs_search.isin.induct)
  case (1 x)
  then show ?case
    apply(subst isin.simps)
    apply (cases ti)
     apply (auto simp add: return_cons_rule)
    done
next
  case (2 ts t x)
  then obtain ls rs where list_split[simp]: "abs_split ts x = (ls,rs)"
    by (cases "abs_split ts x")
  then show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin.simps)
      apply(sep_auto heap: bin_split_imp_abs_split)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
       apply(rule hoare_triple_preI)
       apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
    show ?thesis
    proof (cases "sep = x")
      (* NOTE: no induction required here, only vacuous counter cases generated *)
      case [simp]: True
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin.simps)
        apply(sep_auto heap: bin_split_imp_abs_split)
         apply(rule hoare_triple_preI)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
        done
    next
      case [simp]: False
      show ?thesis
        apply(simp split: list.splits prod.splits)
        apply safe
        using False apply simp
        apply(subst isin.simps)
        apply(sep_auto heap: bin_split_imp_abs_split)
          (*eliminate vacuous case*)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!:  mod_starD list_assn_len)[]
          (* simplify towards induction step *)
        apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]

(* NOTE show that z = (suba, sepa) *)
        apply(rule norm_pre_ex_rule)+
        apply(rule hoare_triple_preI)
        subgoal for p tsi n ti xsi suba sepa zs1 z zs2 _
          apply(subgoal_tac "z = (suba, sepa)", simp)
          using 2(3) apply(sep_auto heap:"2.IH"(2)[of ls rs h rrs sub sep] simp add: sorted_wrt_append)
          using list_split Cons h_split apply simp_all
            (* proof that previous assumptions hold later *)
          apply(rule P_imp_Q_implies_P)
          apply(rule ent_ex_postI[where ?x="(tsi,n)"])
          apply(rule ent_ex_postI[where ?x="ti"])
          apply(rule ent_ex_postI[where ?x="(zs1 @ (suba, sepa) # zs2)"])
          apply(rule ent_ex_postI[where ?x="zs1"])
          apply(rule ent_ex_postI[where ?x="z"])
          apply(rule ent_ex_postI[where ?x="zs2"])
          apply sep_auto
            (* prove subgoal_tac assumption *)
          apply (metis (no_types, lifting) list_assn_aux_ineq_len list_assn_len nth_append_length star_false_left star_false_right)
          done
            (* eliminate last vacuous case *)
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
        done
    qed
  qed
qed


term Array.set

partial_function (heap) ins' :: "nat \<Rightarrow> 'a \<Rightarrow> ('a::{heap,linorder,default}) btnode ref option \<Rightarrow> 'a btupi Heap"
  where
    "ins' k x p = (case p of
  None \<Rightarrow> 
    return (Up\<^sub>i None x None) |
  (Some a) \<Rightarrow> do {
    node \<leftarrow> !a;
    i \<leftarrow> bin_split (kvs node) x;
    tsl \<leftarrow> pfa_length (kvs node);
    if i < tsl then do {
      s \<leftarrow> pfa_get (kvs node) i;
      let (sub,sep) = s in
      if sep = x then
        return (T\<^sub>i p)
      else do {
        r \<leftarrow> ins' k x sub;
        case r of 
          (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set (kvs node) i (lp,sep);
            return (T\<^sub>i p)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            kvs' \<leftarrow> pfa_set (kvs node) i (rp,sep);
            kvs'' \<leftarrow> pfa_insert_grow kvs' i (lp,x');
            node\<^sub>i k kvs'' (last node)
          }
        }
      }
    else do {
      r \<leftarrow> ins' k x (last node);
      case r of 
        (T\<^sub>i lp) \<Rightarrow> do {
          a := (Btnode (kvs node) lp);
          return (T\<^sub>i p)
        } |
        (Up\<^sub>i lp x' rp) \<Rightarrow> do {
          kvs' \<leftarrow> pfa_append_grow' (kvs node) (lp,x');
          node\<^sub>i k kvs' rp
        }
    }
  }
)"

declare  btree_abs_search.ins.simps [simp]
lemma ins'_rule:
  "sorted_less (inorder t) \<Longrightarrow> <btree_assn k t ti * true>
  ins' k x ti
  <\<lambda>r. btupi_assn k (btree_abs_search.ins k x t) r>\<^sub>t"
proof (induction k x t arbitrary: ti rule: btree_abs_search.ins.induct)
  case (1 k x)
  then show ?case
    apply(subst ins'.simps)
    apply (sep_auto simp add: pure_app_eq)
    done
next
  case (2 k x ts t)
  obtain ls rrs where list_split: "abs_split ts x = (ls,rrs)"
    by (cases "abs_split ts x")
  have [simp]: "sorted_less (separators ts)"
    using "2.prems" sorted_inorder_separators by simp
  have [simp]: "sorted_less (inorder t)"
    using "2.prems" sorted_inorder_induct_last by simp
  show ?case
  proof (cases rrs)
    case Nil
    then show ?thesis
    proof (cases "btree_abs_search.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins'.simps)
        apply(sep_auto heap: bin_split_imp_abs_split)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa xc sub sep
          apply(rule hoare_triple_preI)
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split T\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for xi
            apply(cases xi)
            apply sep_auto
            apply sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins'.simps)
        apply(sep_auto heap: bin_split_imp_abs_split)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)                 
        subgoal for p tsil tsin tti tsi' xb xaa xc sub sep
          using Nil list_split 
          by (simp add: Imperative_Loops.list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' xb xaa
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split Up\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for xi
            apply(cases xi)
            apply sep_auto
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have [simp]: "sorted_less (inorder sub)"
      using "2.prems" btree_abs_search.split_axioms list_split Cons sorted_inorder_induct_subtree split_def
      by fastforce
    then show ?thesis
    proof(cases "x = sep")
      case True
      show ?thesis
        apply(subst ins'.simps)
        apply(sep_auto heap: bin_split_imp_abs_split)
        subgoal for p tsil tsin tti tsi j subi
          using Cons list_split a_split True
          by sep_auto
        subgoal for p tsil tsin tti tsi j _ _ subi sepi
          apply(rule hoare_triple_preI)
          using Cons list_split a_split True
          apply(subgoal_tac "sepi = sep")
          apply (sep_auto simp add: split_relation_alt)
          apply(sep_auto simp add: list_assn_prod_map dest!: mod_starD id_assn_list)
          by (metis length_map snd_conv snd_map_help(2) split_relation_access)
        subgoal for p tsil tsin tti tsi j
          apply(rule hoare_triple_preI)
          using Cons list_split
          by (sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
        done
    next
      case False
      then show ?thesis
      proof (cases "btree_abs_search.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins'.simps)
          apply vcg
          apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
            apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply (cases a, simp)
            apply(subgoal_tac "subi = suba", simp)
            using list_split a_split T\<^sub>i False
            apply (vcg heap: 2)
            apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
            apply vcg
            apply simp
            apply vcg
            apply simp
            subgoal for a'i q r
              apply(rule impI)
              apply(simp add: list_assn_append_Cons_left)
              apply(rule ent_ex_postI[where ?x="(tsil,tsin)"])
              apply(rule ent_ex_postI[where ?x="ti"])
              apply(rule ent_ex_postI[where ?x="(zs1 @ (a'i, sepi) # zs2)"])
              apply(rule ent_ex_postI[where ?x="zs1"])
              apply(rule ent_ex_postI[where ?x="(a'i,sep)"])
              apply(rule ent_ex_postI[where ?x="zs2"])
              apply sep_auto
              apply (simp add: pure_app_eq)
              apply(sep_auto dest!:  mod_starD list_assn_len)[]
              done
            apply (metis Imperative_Loops.list_assn_aux_ineq_len Pair_inject list_assn_len nth_append_length star_false_left star_false_right)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins'.simps)
          apply vcg
          apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
          apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
            apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply(subgoal_tac "subi = suba", simp)
            thm 2(2)[of ls rrs a rs sub sep]
            using list_split a_split Cons Up\<^sub>i False
            apply (sep_auto heap: 2(2))
            apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
            apply vcg
            apply simp
            subgoal for x21 x22 x23 u
              apply (cases u,simp)
              thm pfa_insert_grow_rule[where ?l="((zs1 @ (suba, sepi) # zs2)[length ls := (x23, sepa)])"]
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
              apply (simp add: is_pfarray_cap_def)[]
              apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
              apply(auto split: prod.splits  dest!: mod_starD list_assn_len)[]

              apply (vcg heap: node\<^sub>i_rule_ins2)
              apply simp
              apply simp
              apply simp
              apply sep_auto
              done
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      qed
    qed
  qed
qed

declare btree_abs_search.ins.simps[simp del]

(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a btree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)" 

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert' :: "nat \<Rightarrow> ('a::{heap,default,linorder}) \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option Heap" where
"insert' \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins' k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return (Some t')
      }
}"

lemma insert'_rule:
  assumes "k > 0" "sorted_less (inorder t)"
  shows "<btree_assn k t ti * true>
  insert' k x ti
  <\<lambda>r. btree_assn k (btree_abs_search.insert k x t) r>\<^sub>t"
  unfolding insert'_def
  apply(cases "btree_abs_search.ins k x t")
   apply(sep_auto split!: btupi.splits heap: ins'_rule[OF assms(2)])
  using assms
  apply(vcg heap: ins'_rule[OF assms(2)])
  apply(simp split!: btupi.splits)
  apply(vcg)
   apply simp
  apply simp
  apply vcg
  apply auto[]
  subgoal for x21 x22 x23 x21a x22a x23a a b xa
    apply(rule ent_ex_postI[where ?x="(a,b)"])
    apply(rule ent_ex_postI[where ?x="x23a"])
    apply(rule ent_ex_postI[where ?x="[(x21a, x22a)]"])
    apply sep_auto
    done
  done


end

