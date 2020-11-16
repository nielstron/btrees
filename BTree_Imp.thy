theory BTree_Imp
  imports
    "Separation_Logic_Imperative_HOL.Sep_Main"
    Imperative_Loops
    BTree_Set
begin


term sorted


datatype 'a btnode = Btnode "('a btnode ref option*'a) array" "'a btnode ref option"
text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option*'a) array" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

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

    
fun btree_assn where
"btree_assn Leaf None = emp" |
"btree_assn (Node ts t) (Some a) = 
 (\<exists>\<^sub>A tsi ti xsi. 
      a \<mapsto>\<^sub>r Btnode tsi ti 
    * btree_assn t ti 
    * tsi \<mapsto>\<^sub>a xsi
    * list_assn (btree_assn \<times>\<^sub>a id_assn) ts xsi
    )" |
"btree_assn _ _ = false"


find_consts name: while

term split_fun

definition split :: "('a::heap \<times> 'b::{heap,linorder}) array \<Rightarrow> 'b \<Rightarrow> nat Heap"
where
"split a p \<equiv> do {
  l \<leftarrow> Array.len a;
  
  i\<leftarrow>heap_WHILET 
    (\<lambda>i. if i<l then do {
      (_,s) \<leftarrow> Array.nth a i;
      return (s<p)
    } else return False) 
    (\<lambda>i. return (i+1)) 
    0;
       
  return i
}"

lemma split_rule: "< a \<mapsto>\<^sub>a xs * true > split a p <\<lambda>i. a\<mapsto>\<^sub>a xs * \<up>(i\<le>length xs \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<length xs \<longrightarrow> snd (xs!i)\<ge>p)) >\<^sub>t"
  unfolding split_def
  
  supply R = heap_WHILET_rule''[where 
    R = "measure (\<lambda>i. length xs - i)"
    and I = "\<lambda>i. a\<mapsto>\<^sub>a xs * \<up>(i\<le>length xs \<and> (\<forall>j<i. snd (xs!j) < p))"
    and b = "\<lambda>i. i<length xs \<and> snd (xs!i) < p"
  ]
  
  apply (sep_auto decon: R simp: less_Suc_eq) []
  done


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  apply(cases "a < b")
   apply auto
  done
  
  
definition "abs_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"

definition "split_relation xs \<equiv> \<lambda>(as,bs) i. as=take i xs \<and> bs = drop i xs"

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
  apply(induct rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj)
  done

(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done



lemma id_assn_pure: "id_assn = \<up>\<circ>\<circ>(=)"
  by fastforce

(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn xs ys \<Longrightarrow> (\<forall>i<length xs. (xs!i) = (ys!i))"
  apply(simp add: id_assn_pure)
  using list_assn_all[of "(=)" xs ys h] by metis

lemma list_assn_len: "h \<Turnstile> list_assn A xs ys \<Longrightarrow> length xs = length ys"
  using list_assn_aux_ineq_len by fastforce

lemma snd_map_help:
    "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
    "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto

lemma "<
    a \<mapsto>\<^sub>a tsi 
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi
  * true> 
    split a p 
  <\<lambda>i. 
    a\<mapsto>\<^sub>a tsi 
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>( split_relation ts (abs_split ts p) i)>\<^sub>t"
  apply (sep_auto heap: split_rule
 simp add: list_assn_prod_map split_ismeq)
proof -
  fix h assume heap_init: "h \<Turnstile> a \<mapsto>\<^sub>a tsi *list_assn id_assn (map snd ts) (map snd tsi) *
       list_assn A (map fst ts) (map fst tsi) * true"
  then have tsi_ts_eq_elems: "\<forall>j < length (map snd tsi). ((map snd tsi)!j) = ((map snd ts)!j)"
    by (metis (mono_tags, lifting) id_assn_list list_assn_aux_ineq_len mod_starD)

  from heap_init have map_tsi_ts_eq: "length (map snd tsi) = length (map snd ts)"
    by (metis list_assn_aux_ineq_len list_assn_len star_false_left star_false_right)

  show full_thm: "\<forall>j<length tsi. snd (tsi ! j) < p \<Longrightarrow>
       split_relation ts (abs_split ts p) (length tsi)"
  proof -
    assume sm_list: "\<forall>j<length tsi. snd (tsi ! j) < p"
    then have "\<forall>j < length (map snd tsi). ((map snd tsi)!j) < p"
      by simp
    then have "\<forall>j<length (map snd ts). ((map snd ts)!j) < p"
      using tsi_ts_eq_elems map_tsi_ts_eq by metis
    then have "\<forall>(_,s) \<in> set ts. s < p"
      by (metis case_prod_unfold in_set_conv_nth length_map nth_map)
    then have "abs_split ts p = (ts, [])"
      using abs_split_full[of ts p] by simp
    then show "split_relation ts (abs_split ts p) (length tsi)"
      using
        \<open>length (map snd tsi) = length (map snd ts)\<close>
        split_relation_length
      by auto
  qed
  then show "\<forall>j<length tsi. snd (tsi ! j) < p \<Longrightarrow>
       p \<le> snd (tsi ! length tsi) \<Longrightarrow>
       split_relation ts (abs_split ts p) (length tsi)"
    by simp

  show part_thm: "\<And>x. x < length tsi \<Longrightarrow>
       \<forall>j<x. snd (tsi ! j) < p \<Longrightarrow>
       p \<le> snd (tsi ! x) \<Longrightarrow> split_relation ts (abs_split ts p) x"
  proof -
    fix x assume x_sm_len: "x < length tsi"
    moreover assume sm_list: "\<forall>j<x. snd (tsi ! j) < p"
    ultimately have "\<forall>j<x. ((map snd tsi) ! j) < p"
      by auto
    then have "\<forall>j<x. ((map snd ts)!j) < p"
      using tsi_ts_eq_elems map_tsi_ts_eq x_sm_len
      by auto
    moreover have x_sm_len_ts: "x < length ts"
      using map_tsi_ts_eq x_sm_len by auto
    ultimately have "\<forall>(_,x) \<in> set (take x ts). x < p"
      by (auto simp add: in_set_conv_nth  min.absorb2)+
    moreover assume "p \<le> snd (tsi ! x)"
    then have "case tsi!x of (_,s) \<Rightarrow> \<not>(s < p)"
      by (simp add: case_prod_unfold x_sm_len)
    then have "case ts!x of (_,s) \<Rightarrow> \<not>(s < p)"
      using tsi_ts_eq_elems x_sm_len x_sm_len_ts by auto
    ultimately have "abs_split ts p = (take x ts, drop x ts)"
      using x_sm_len_ts abs_split_split[of x ts p]
      by metis
    then show "split_relation ts (abs_split ts p) x"
      by (auto simp add: split_relation_def)
  qed
qed

(*
  apply (sep_auto) []
  apply (sep_auto) []
  apply (sep_auto simp: less_Suc_eq) []
  apply (rule ent_refl)
  apply (sep_auto) []
  
    
  thm sep_decon_rules
  apply (sep_auto heap: R simp: less_Suc_eq)
  find_theorems "_ < Suc _" "(\<or>)"
  
  oops
  apply (vcg (ss) heap: R)
  apply (sep_auto) []
  apply (sep_auto) []
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply simp  
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  apply (vcg (ss))
  
*)

(* probably need to assert circle-free ness of the references *)

partial_function (heap) isin :: "('a::{heap,linorder}) btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
where
"isin p x = 
  (case p of 
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> split (kvs node) x;
       tsl \<leftarrow> Array.len (kvs node);
       if i = tsl then 
         isin (last node) x
       else do {
         s \<leftarrow> Array.nth (kvs node) i;
         if snd s = x then
           return True
         else
           isin (fst s) x
       }
    }
)"

definition isin_while :: "('a::{heap,linorder}) btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
where
"isin_while p x \<equiv> do {
  r \<leftarrow> heap_WHILET 
    (\<lambda>p. return ((fst p = None) \<or> (snd p)))
    (\<lambda>p. 
      (case fst p of (Some a) \<Rightarrow> do {
        node \<leftarrow> !a;
        i \<leftarrow> split (kvs node) x;
        tsl \<leftarrow> Array.len (kvs node);
        if i = tsl then 
         return ((last node), False)
        else do {
         s \<leftarrow> Array.nth (kvs node) i;
         return (fst s, snd s = x)
        }
      }
     )) 
    (p, False);
  return (snd r)
}"




end

