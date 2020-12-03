theory Partly_Filled_Array
  imports
 "Imperative_Loops"
 "Refine_Imperative_HOL.IICF_Array_List"

begin

(* MISSING(?): statement about preserving capacities *)

text "An array that is only partly filled.
The number of actual elements contained is kept in a second element.
This represents a weakened version of the array_list from IICF"

type_synonym 'a pfarray = "'a array_list"


section "Operations on Partly Filled Arrays"

definition is_pfarray where
"is_pfarray l \<equiv> \<lambda>(a,n). \<exists>\<^sub>A l'. a \<mapsto>\<^sub>a l' *  \<up>(n \<le> length l' \<and> l = (take n l'))"


definition is_pfarray_cap where
"is_pfarray_cap c l \<equiv> \<lambda>(a,n). \<exists>\<^sub>A l'. a \<mapsto>\<^sub>a l' *  \<up>(c = length l' \<and> n \<le> length l' \<and> l = (take n l'))"

  lemma is_pfarray_prec[safe_constraint_rules]: "precise is_pfarray"
    unfolding is_pfarray_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits) 
  	using preciseD snga_prec by fastforce

  lemma is_pfarray_cap_prec[safe_constraint_rules]: "precise (is_pfarray_cap c)"
    unfolding is_pfarray_cap_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits) 
  	using preciseD snga_prec by fastforce

lemma pfarray_cap_stronger: "is_pfarray_cap c l a \<Longrightarrow>\<^sub>A is_pfarray l a"
  by (sep_auto simp add: is_pfarray_cap_def is_pfarray_def split: prod.splits)

definition pfa_empty where
"pfa_empty cap \<equiv> do {
  a \<leftarrow> Array.new cap default;
  return (a,0::nat)
}"

definition "pfa_append \<equiv> \<lambda>(a,n) x. do {
  a \<leftarrow> Array.upd n x a;
  return (a,n+1)
}"


definition "pfa_last \<equiv> arl_last"

definition pfa_butlast :: "'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
  "pfa_butlast \<equiv> \<lambda>(a,n).
    return (a,n-1)
  "

definition "pfa_get \<equiv> arl_get"

definition "pfa_length \<equiv> arl_length"

definition "pfa_capacity \<equiv> \<lambda>(a,n). do {
  l \<leftarrow> Array.len a;
  return l
}
"


definition "pfa_is_empty \<equiv> arl_is_empty"

definition "pfa_set \<equiv> arl_set"

definition pfa_shrink :: "nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
"pfa_shrink k \<equiv> \<lambda>(a,n).
  return (a,k)
"

definition pfa_shrink_cap :: "nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
"pfa_shrink_cap k \<equiv> \<lambda>(a,n). do {
  a' \<leftarrow> array_shrink a k;
  return (a',min k n)
}
"


definition "pfa_copy \<equiv> arl_copy"

term blit

definition pfa_blit :: "'a::heap pfarray \<Rightarrow> nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
"pfa_blit \<equiv> \<lambda>(src,sn) si (dst,dn) di l. do {
   blit src si dst di l;
   return ()
}
"

definition pfa_drop :: "('a::heap) pfarray \<Rightarrow> nat \<Rightarrow> 'a pfarray \<Rightarrow> 'a pfarray Heap" where
"pfa_drop \<equiv> \<lambda>(src,sn) si (dst,dn). do {
   blit src si dst 0 (sn-si);
   return (dst,(sn-si))
}
"

term arl_append


definition "pfa_append_grow \<equiv> \<lambda>(a,n) x. do {
  l \<leftarrow> pfa_capacity (a,n);
  a' \<leftarrow> if l = n 
  then array_grow a (l+1) x
  else Array.upd n x a;
  return (a',n+1)
}"




section "Inference rules"

lemma pfa_empty_rule[sep_heap_rules]: "< emp > pfa_empty N <is_pfarray_cap N []>"
  by (sep_auto simp: pfa_empty_def arl_empty_def is_pfarray_cap_def)

lemma pfa_length_rule[sep_heap_rules]: "
  <is_pfarray_cap c l a> 
    pfa_length a
  <\<lambda>r. is_pfarray_cap c l a * \<up>(r=length l)>"
  by (sep_auto simp: pfa_length_def arl_length_def is_pfarray_cap_def)

lemma pfa_capacity_rule[sep_heap_rules]: "
  <is_pfarray_cap c l a> 
    pfa_capacity a
  <\<lambda>r. is_pfarray_cap c l a * \<up>(c=r)>"
  by (sep_auto simp: pfa_capacity_def arl_length_def is_pfarray_cap_def)


  lemma pfa_is_empty_rule[sep_heap_rules]: "
    <is_pfarray_cap c l a> 
      pfa_is_empty a
    <\<lambda>r. is_pfarray_cap c l a * \<up>(r\<longleftrightarrow>(l=[]))>"
    by (sep_auto simp: pfa_is_empty_def arl_is_empty_def is_pfarray_cap_def)

lemma pfa_append_rule[sep_heap_rules]: "
   n < c  \<Longrightarrow>
    < is_pfarray_cap c l (a,n) > 
      pfa_append (a,n) x 
    <\<lambda>(a',n'). is_pfarray_cap c (l@[x]) (a',n') * \<up>(a' = a) >"  
    by (sep_auto 
      simp: pfa_append_def arl_append_def is_pfarray_cap_def take_update_last neq_Nil_conv
      split: prod.splits nat.split)

lemma pfa_last_rule[sep_heap_rules]: "
  l\<noteq>[] \<Longrightarrow>
  <is_pfarray_cap c l a> 
    pfa_last a
  <\<lambda>r. is_pfarray_cap c l a * \<up>(r=last l)>"
  by (sep_auto simp: pfa_last_def arl_last_def is_pfarray_cap_def last_take_nth_conv)

lemma pfa_butlast_rule[sep_heap_rules]: "
  <is_pfarray_cap c l (a,n)> 
    pfa_butlast (a,n)
  <\<lambda>(a',n'). is_pfarray_cap c (butlast l) (a',n') * \<up>(a' = a)>"
    by (sep_auto 
      split: prod.splits
      simp: pfa_butlast_def is_pfarray_cap_def butlast_take)  


lemma pfa_get_rule[sep_heap_rules]: "
  i < length l \<Longrightarrow>
  < is_pfarray_cap c l a> 
    pfa_get a i
  <\<lambda>r. is_pfarray_cap c l a * \<up>((l!i) = r)>"
  apply (sep_auto simp: is_pfarray_cap_def pfa_get_def arl_get_def  split: prod.split)
  done

  lemma pfa_set_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_pfarray_cap c l a> 
      pfa_set a i x
    <\<lambda>a'. is_pfarray_cap c (l[i:=x]) a' * \<up>(a' = a)>"
    by (sep_auto simp: pfa_set_def arl_set_def is_pfarray_cap_def split: prod.split)

lemma pfa_shrink_rule[sep_heap_rules]: "
   k \<le> length l \<Longrightarrow>
    < is_pfarray_cap c l (a,n) > 
      pfa_shrink k (a,n)
    <\<lambda>(a',n'). is_pfarray_cap c (take k l) (a',n') * \<up>(n' = k) * \<up>(a'=a) >"  
  by (sep_auto 
      simp: pfa_shrink_def is_pfarray_cap_def min.absorb1
      split: prod.splits nat.split)

lemma pfa_shrink_cap_rule_preserve[sep_heap_rules]: "
   \<lbrakk>n \<le> k; k \<le> c\<rbrakk> \<Longrightarrow>
    < is_pfarray_cap c l (a,n) > 
      pfa_shrink_cap k (a,n)
    <\<lambda>a'. is_pfarray_cap k l a' >\<^sub>t"
  by (sep_auto 
      simp: pfa_shrink_cap_def is_pfarray_cap_def min.absorb1 min.absorb2
      split: prod.splits nat.split)



lemma pfa_shrink_cap_rule: "
   \<lbrakk>k \<le> c\<rbrakk> \<Longrightarrow>
    < is_pfarray_cap c l a > 
      pfa_shrink_cap k a
    <\<lambda>a'. is_pfarray_cap k (take k l) a' >\<^sub>t"  
  by (sep_auto 
      simp: pfa_shrink_cap_def is_pfarray_cap_def min.absorb1 min.absorb2
      split: prod.splits nat.split dest: mod_starD)



lemma pfa_copy_rule[sep_heap_rules]: "< is_pfarray_cap c l a > pfa_copy a <\<lambda>r. is_pfarray_cap c l a * is_pfarray_cap c l r>\<^sub>t"  
    by (sep_auto simp: pfa_copy_def arl_copy_def is_pfarray_cap_def)

lemma min_nat: "min a (a+b) = (a::nat)"
  by auto


lemma pfa_blit_rule[sep_heap_rules]:
    assumes LEN: "si+len \<le> sn" "di \<le> dn" "di+len \<le> dc"
    shows
    "< is_pfarray_cap sc src (srci,sn)
      * is_pfarray_cap dc dst (dsti,dn) >
    pfa_blit (srci,sn) si (dsti,dn) di len
    <\<lambda>_. is_pfarray_cap sc src (srci,sn)
      * is_pfarray_cap dc (take di dst @ take len (drop si src) @ drop (di+len) dst) (dsti,max (di+len) dn)
    >\<^sub>t"
  using LEN apply(sep_auto simp add: min_nat is_pfarray_cap_def pfa_blit_def min.commute min.absorb1 heap: blit_rule)
   apply (simp add: min.absorb1 take_drop)
   apply (simp add: drop_take max_def)
  done

lemma pfa_drop_rule[sep_heap_rules]:
    assumes LEN: "si \<le> sn" "(sn-si) \<le> dc"
    shows
    "< is_pfarray_cap sc src (srci,sn)
      * is_pfarray_cap dc dst (dsti,dn) >
    pfa_drop (srci,sn) si (dsti,dn)
    <\<lambda>(dsti',dn'). is_pfarray_cap sc src (srci,sn)
      * is_pfarray_cap dc (drop si src) (dsti',dn')
      * \<up>(dsti' = dsti)
    >\<^sub>t"
  using LEN apply (sep_auto simp add: drop_take is_pfarray_cap_def pfa_drop_def dest!: mod_starD heap: pfa_blit_rule)
  done

lemma pfa_append_grow_full_rule: "n = c \<Longrightarrow>
     <is_pfarray_cap c l (a,n)>
  array_grow a (c+1) x
      <\<lambda>a'. is_pfarray_cap (c+1) (l@[x]) (a',n+1)>\<^sub>t"
  apply(sep_auto simp add: is_pfarray_cap_def 
heap del: array_grow_rule)
  apply(vcg heap del: array_grow_rule heap add: array_grow_rule[of l "(Suc (length l))" a x])
   apply simp
  apply(rule ent_ex_postI[where ?x="l@[x]"])
  apply sep_auto
  done


lemma pfa_append_grow_less_rule: "n < c \<Longrightarrow>
 <is_pfarray_cap c l (a,n)>
    Array.upd n x a
<\<lambda>a'. is_pfarray_cap c (l@[x]) (a',n+1)>\<^sub>t"
  apply(sep_auto simp add: is_pfarray_cap_def take_update_last)
  done

lemma pfa_append_grow_rule: "
  <is_pfarray_cap c l (a,n)>
  pfa_append_grow (a,n) x 
  <\<lambda>(a',n'). is_pfarray_cap (if c = n then c+1 else c) (l@[x]) (a',n') * \<up>(n'=n+1)>\<^sub>t"
  apply(subst pfa_append_grow_def)
  apply(rule hoare_triple_preI)
  apply (sep_auto
      heap add: pfa_append_grow_full_rule pfa_append_grow_less_rule)
   apply(sep_auto simp add: is_pfarray_cap_def)
  apply(sep_auto simp add: is_pfarray_cap_def)
  done




 definition "pfa_assn A \<equiv> hr_comp is_pfarray (\<langle>the_pure A\<rangle>list_rel)"
  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "pfa_assn A" for A]


  lemma pfa_assn_comp: "is_pure A \<Longrightarrow> hr_comp (pfa_assn A) (\<langle>B\<rangle>list_rel) = pfa_assn (hr_comp A B)"
    unfolding pfa_assn_def
    by (auto simp: hr_comp_the_pure hr_comp_assoc list_rel_compp)

  lemma pfa_assn_comp': "hr_comp (pfa_assn id_assn) (\<langle>B\<rangle>list_rel) = pfa_assn (pure B)"
    by (simp add: pfa_assn_comp)

context 
  notes [fcomp_norm_unfold] = pfa_assn_def[symmetric] pfa_assn_comp'
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin  


  lemma pfa_empty_hnr_aux: "(uncurry0 (pfa_empty N),uncurry0 (RETURN op_list_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_pfarray"  
    sorry
  sepref_decl_impl (no_register) pfa_empty: pfa_empty_hnr_aux .

  definition "op_pfa_empty (N::nat) \<equiv> op_list_empty"

  lemma pfa_length_hnr_aux: "(pfa_length,RETURN o op_list_length) \<in> is_pfarray\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    by sep_auto
  sepref_decl_impl pfa_length: pfa_length_hnr_aux .

  lemma pfa_is_empty_hnr_aux: "(pfa_is_empty,RETURN o op_list_is_empty) \<in> is_pfarray\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    by sep_auto
  sepref_decl_impl pfa_is_empty: pfa_is_empty_hnr_aux .  

lemma pfa_last_hnr_aux: "(pfa_last,RETURN o op_list_last) \<in> [pre_list_last]\<^sub>a is_pfarray\<^sup>k \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl pfa_last: pfa_last_hnr_aux . 

  lemma pfa_butlast_hnr_aux: "(pfa_butlast,RETURN o op_list_butlast) \<in> [pre_list_butlast]\<^sub>a is_pfarray\<^sup>d \<rightarrow> is_pfarray"
    by sep_auto
  sepref_decl_impl pfa_butlast: pfa_butlast_hnr_aux .

  lemma pfa_get_hnr_aux: "(uncurry pfa_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_pfarray\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
    by sep_auto
  sepref_decl_impl pfa_get: pfa_get_hnr_aux .

  lemma pfa_set_hnr_aux: "(uncurry2 pfa_set,uncurry2 (RETURN ooo op_list_set)) \<in> [\<lambda>((l,i),_). i<length l]\<^sub>a (is_pfarray\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k) \<rightarrow> is_pfarray"
    by sep_auto
  sepref_decl_impl pfa_set: pfa_set_hnr_aux .

  sepref_definition pfa_swap is "uncurry2 mop_list_swap" :: "((pfa_assn id_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pfa_assn id_assn)"
    unfolding gen_mop_list_swap[abs_def]
    by sepref
  sepref_decl_impl (ismop) pfa_swap: pfa_swap.refine .  
end


lemma [def_pat_rules]: "op_pfa_empty$N \<equiv> UNPROTECT (op_pfa_empty N)" by simp
interpretation pfa_sz: list_custom_empty "pfa_assn A" "pfa_empty N" "PR_CONST (op_pfa_empty N)"
  apply unfold_locales
  apply (rule pfa_empty_hnr)
  by (auto simp: op_pfa_empty_def)


end