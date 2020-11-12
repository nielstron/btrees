theory Test_imp
imports Main 
  "../isabelle_llvm/thys/ds/LLVM_DS_Dflt"
  "../isabelle_llvm/thys/ds/LLVM_DS_Array_List"
  "../isabelle_llvm/thys/ds/Proto_EOArray"
begin

(* TODO: Move *)
definition prod_assn :: "('a1,'c1) dr_assn \<Rightarrow> ('a2,'c2) dr_assn
  \<Rightarrow> ('a1*'a2, 'c1*'c2) dr_assn" where
  "prod_assn P1 P2 = mk_assn (\<lambda>(a,b) (ai,bi). \<upharpoonleft>P1 a ai ** \<upharpoonleft> P2 b bi )"

notation prod_assn (infixr "\<times>\<^sub>a" 70)

lemma prod_assn_pair_conv[simp]: 
  "\<upharpoonleft>(prod_assn A B) (a1,b1) (a2,b2) = (\<upharpoonleft>A a1 a2 ** \<upharpoonleft>B b1 b2)"
  unfolding prod_assn_def by auto

  
  
  

  datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

  type_synonym size_t = "64"
  
  datatype 'a btnode = NXAA "('a btnode ptr \<times> 'a, size_t) array_list" "'a btnode ptr"
  

  struct btnode;
  
  struct btnode {
    btnode ..
  
  }
    
  
  
  
  abbreviation "id_assn \<equiv> mk_pure_assn (=)"
  
  term list_assn
  
  fun assn_btree_aux :: "'a btree \<Rightarrow> ( \<times>   ) ptr" where
    "assn_btree_aux Leaf ptr = ( \<up>(ptr=null) )"
  | "assn_btree_aux (Node ts t) ptr = (EXS tsi\<^sub>1 tsi\<^sub>2 ti. 
        \<upharpoonleft>ll_pto (tsi\<^sub>1,ti) ptr 
     ** \<upharpoonleft>arl_assn tsi\<^sub>2 tsi\<^sub>1  
     \<^cancel>\<open>** \<upharpoonleft>(list_assn (mk_assn assn_btree_aux \<times>\<^sub>a id_assn)) ts tsi\<^sub>2\<close>
        
        
        
        )"
  
    

end
