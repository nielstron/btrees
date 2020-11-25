theory BTree_Imp_DynArray
  imports
    "Refine_Imperative_HOL.IICF_Array_List"
    Imperative_Loops
    BTree_Set
begin


datatype 'a btnode =
  Btnode "('a btnode ref option*'a) array_list" "'a btnode ref option"

text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option*'a) array_list" where
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


    
fun btree_assn :: "'a::heap btree \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
"btree_assn Leaf None = emp" |
"btree_assn (Node ts t) (Some a) = 
 (\<exists>\<^sub>A tsi ti tsi' n l'. 
      a \<mapsto>\<^sub>r Btnode tsi ti 
    * btree_assn t ti
    * \<up>(tsi = (tsi', n))
    * tsi' \<mapsto>\<^sub>a l'
    * \<up>(n \<le> length l')
    * list_assn (btree_assn \<times>\<^sub>a id_assn) ts (take n l')
    )" |
"btree_assn _ _ = false"

function (sequential) btree_assn_simpd :: "'a::heap btree \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
"btree_assn_simpd Leaf None = emp" |
"btree_assn_simpd (Node ts t) (Some a) =
     (\<exists>\<^sub>A tsi ti. 
        a \<mapsto>\<^sub>r Btnode tsi ti 
        * btree_assn_simpd t ti
        * array_list_assn (btree_assn_simpd \<times>\<^sub>a id_assn) ts tsi
      )
" |
"btree_assn_simpd _ _ = false"
  apply(auto)
  by (metis btree.exhaust not_Some_eq)


find_consts name: while

term split_fun

definition split :: "('a::heap \<times> 'b::{heap,linorder}) array_list \<Rightarrow> 'b \<Rightarrow> nat Heap"
where
"split l p \<equiv> 
  let (a,n) = l in do {
  
  i \<leftarrow> heap_WHILET 
    (\<lambda>i. if i<n then do {
      (_,s) \<leftarrow> Array.nth a i;
      return (s<p)
    } else return False) 
    (\<lambda>i. return (i+1)) 
    0;
       
  return i
}"

lemma split_rule: "n \<le> length xs \<Longrightarrow> < a \<mapsto>\<^sub>a xs * true> split (a,n) p <\<lambda>i. a\<mapsto>\<^sub>a xs * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p)) >\<^sub>t"
  unfolding split_def
  
  supply R = heap_WHILET_rule''[where 
    R = "measure (\<lambda>i. n - i)"
    and I = "\<lambda>i. a\<mapsto>\<^sub>a xs * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p))"
    and b = "\<lambda>i. i<n \<and> snd (xs!i) < p"
  ]
  thm R
  
  apply (sep_auto decon: R simp: less_Suc_eq) []
  done


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  apply(cases "a < b")
   apply auto
  done
  
  
definition "abs_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"

interpretation btree_abs_search: split_fun abs_split
  apply unfold_locales
  unfolding abs_split_def
  apply (auto simp: split: list.splits)
  subgoal
    by (meson case_prodD set_takeWhileD)
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


lemma snd_map_help:
    "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
    "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto

find_theorems "<_>_<_>"

lemma split_imp_abs_split: "n \<le> length tsi \<Longrightarrow> <
    a \<mapsto>\<^sub>a tsi 
  * list_assn (A \<times>\<^sub>a id_assn) ts (take n tsi)
  * true> 
    split (a,n) p 
  <\<lambda>i. 
      a \<mapsto>\<^sub>a tsi
    * list_assn (A \<times>\<^sub>a id_assn) ts (take n tsi)
    * \<up>(split_relation ts (abs_split ts p) i)>\<^sub>t"
  thm split_rule
  apply (sep_auto heap: split_rule
 simp add: list_assn_prod_map split_ismeq)
proof -
  assume n_len: "n \<le> length tsi"
  fix h assume heap_init: "h \<Turnstile> a \<mapsto>\<^sub>a tsi * list_assn id_assn (map snd ts) (map snd (take n tsi)) *
       list_assn A (map fst ts) (map fst (take n tsi)) * true"
  then have tsi_ts_eq_elems: "\<forall>j < length (map snd (take n tsi)). ((map snd (take n tsi))!j) = ((map snd ts)!j)"
    by (metis (mono_tags, lifting) id_assn_list list_assn_aux_ineq_len mod_starD)

  from heap_init have map_tsi_ts_eq: "length (map snd (take n tsi)) = length (map snd ts)"
    by (metis list_assn_aux_ineq_len list_assn_len star_false_left star_false_right)
  then have map_n_ts_eq: "n = length (map snd ts)"
    using n_len by auto


  show full_thm: "\<forall>j<n. snd (tsi ! j) < p \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
  proof -
    assume sm_list: "\<forall>j<n. snd (tsi ! j) < p"
    then have "\<forall>j < length (map snd (take n tsi)). ((map snd (take n tsi))!j) < p"
      by simp
    then have "\<forall>j<length (map snd ts). ((map snd ts)!j) < p"
      using tsi_ts_eq_elems map_tsi_ts_eq by metis
    then have "\<forall>(_,s) \<in> set ts. s < p"
      by (metis case_prod_unfold in_set_conv_nth length_map nth_map)
    then have "abs_split ts p = (ts, [])"
      using abs_split_full[of ts p] by simp
    then show "split_relation ts (abs_split ts p) n"
      using
        map_n_ts_eq
        split_relation_length
        n_len
      by auto
      
  qed
  then show "\<forall>j<n. snd (tsi ! j) < p \<Longrightarrow>
       p \<le> snd (tsi ! n) \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
    by simp

  show part_thm: "\<And>x. x < n \<Longrightarrow>
       \<forall>j<x. snd (tsi ! j) < p \<Longrightarrow>
       p \<le> snd (tsi ! x) \<Longrightarrow> split_relation ts (abs_split ts p) x"
  proof -
    fix x assume x_sm_len: "x < n"
    moreover assume sm_list: "\<forall>j<x. snd (tsi ! j) < p"
    ultimately have "\<forall>j<x. ((map snd tsi) ! j) < p"
      using n_len
      by auto
    then have "\<forall>j<x. ((map snd ts)!j) < p"
      using tsi_ts_eq_elems map_tsi_ts_eq x_sm_len n_len
      by auto
    moreover have x_sm_len_ts: "x < n"
      using map_tsi_ts_eq x_sm_len by auto
    ultimately have "\<forall>(_,x) \<in> set (take x ts). x < p"
      by (auto simp add: in_set_conv_nth  min.absorb2)+
    moreover assume "p \<le> snd (tsi ! x)"
    then have "case tsi!x of (_,s) \<Rightarrow> \<not>(s < p)"
      by (simp add: case_prod_unfold x_sm_len)
    then have "case ts!x of (_,s) \<Rightarrow> \<not>(s < p)"
      using tsi_ts_eq_elems x_sm_len x_sm_len_ts n_len
      by (metis (mono_tags, lifting) case_prod_unfold length_map map_n_ts_eq map_tsi_ts_eq nth_take snd_map_help(2))
    ultimately have "abs_split ts p = (take x ts, drop x ts)"
      using x_sm_len_ts abs_split_split[of x ts p] map_n_ts_eq
      by auto
    then show "split_relation ts (abs_split ts p) x"
      using x_sm_len_ts map_n_ts_eq 
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


partial_function (heap) isin :: "('a::{heap,linorder}) btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
where
"isin p x = 
  (case p of 
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> split (kvs node) x;
       let tsl = snd (kvs node) in
       if i < tsl then do {
         s \<leftarrow> arl_get (kvs node) i;
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

lemma  "<btree_assn t ti * true> isin ti x <\<lambda>r. btree_assn t ti * \<up>(btree_abs_search.isin t x = r)>\<^sub>t"
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
      apply(simp split: list.splits prod.splits)
      apply(subst isin.simps)
      apply(sep_auto heap: split_imp_abs_split)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
       apply(rule hoare_triple_preI)
       apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      aapply(sep_auto heap: "2.IH"(1)[of ls "[]"])
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
        apply(sep_auto heap: split_imp_abs_split)
         apply(rule hoare_triple_preI)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest: sym[of "[]"] mod_starD list_assn_len)[]
        done
    next
      case [simp]: False
      show ?thesis
        apply(simp split: list.splits prod.splits)
        apply safe
        using False apply simp
        apply(subst isin.simps)
        apply(sep_auto heap: split_imp_abs_split)
          (*eliminate vacuous case*)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!:  mod_starD list_assn_len)[]
        (* simplify towards induction step *)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]

        (* NOTE show that z = (suba, sepa) *)
         apply(rule norm_pre_ex_rule)+
         apply(rule hoare_triple_preI)
        subgoal for p tsi ti xsi suba sepa zs1 z zs2 _
          apply(subgoal_tac "z = (suba, sepa)", simp)
           apply(sep_auto heap:"2.IH"(2)[of ls rs h rrs sub sep])
          using list_split Cons h_split apply simp_all
            (* proof that previous assumptions hold later *)
          apply(rule P_imp_Q_implies_P)
          apply(rule ent_ex_postI[where ?x="tsi"])
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

lemma  "<btree_assn t ti * true > isin_while ti x <\<lambda>r. btree_assn t ti * \<up>(btree_abs_search.isin t x = r)>\<^sub>t"
  unfolding isin_while_def
  oops


definition split_half :: "('a::heap \<times> 'b::{heap}) array \<Rightarrow> nat Heap"
where
"split_half a \<equiv> do {
  l \<leftarrow> Array.len a;
  return (l div 2)
}"

lemma split_half_rule: "<
    a \<mapsto>\<^sub>a tsi 
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi
  * true> 
    split_half a
  <\<lambda>i. 
      a \<mapsto>\<^sub>a tsi 
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>( split_relation ts (BTree_Set.split_half ts) i)>\<^sub>t"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done

datatype 'a btupi = 
  UpT_i "'a btnode ref option" "'a option" "'a btnode ref option"

fun
  btupi_encode :: "'a::heap btupi \<Rightarrow> nat"
  where
  "btupi_encode (UpT_i a x b) = to_nat (a,x,b)"

thm btupi_encode.cases
instance btupi :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI[of "btupi_encode"])
  subgoal
  proof -
    fix x :: "'a btupi" and y :: "'a btupi"
    assume a1: "btupi_encode x = btupi_encode y"
    have "\<forall>b n. (\<exists>z za zb. to_nat (z, za::'a option, zb) = n \<and> UpT_i z za zb = b) \<or> btupi_encode b \<noteq> n"
      by (metis (no_types) btupi_encode.elims)
    then show "x = y"
      using a1 by (metis Pair_inject from_nat_to_nat)
  qed
  ..

fun btupi_assn where
"btupi_assn (btree_abs_search.T_i l) (UpT_i li None None) = btree_assn l li" |
"btupi_assn (btree_abs_search.Up_i l a r) (UpT_i li (Some ai) ri) = btree_assn l li * id_assn a ai * btree_assn r ri" |
"btupi_assn _ _ = false"

find_theorems Array

term blit

thm list_assn.simps
find_theorems slice

term is_array_list



definition node_i :: "nat \<Rightarrow> (('a::heap) btnode ref option \<times> 'a) array_list \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap" where
"node_i k (a,n) ti \<equiv> do {
    l \<leftarrow> ref (Btnode a ti);
    if n \<le> 2*k then
      return (UpT_i (Some l) None None)
    else do {
      i \<leftarrow> split_half a;
      return ()
    }
}"

end

