theory BTree_Imp
  imports "Separation_Logic_Imperative_HOL.Sep_Main"
begin

datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

datatype 'a btnode = Btnode "('a btnode ref option*'a) array" "'a
btnode ref option"

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

  
context fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> assn"
begin
  fun list_assn where
    "list_assn [] [] = emp"
  | "list_assn (x#xs) (y#ys) = A x y * list_assn xs ys"  
  | "list_assn _ _ = false"
end


lemma list_assn_cong[fundef_cong]:
  "\<lbrakk> xs=xs'; ys=ys'; \<And>x y. \<lbrakk> x\<in>set xs; y\<in>set ys \<rbrakk> \<Longrightarrow> A x y = A' x y \<rbrakk> \<Longrightarrow>
list_assn A xs ys = list_assn A' xs' ys'"
  apply (induction xs ys arbitrary: xs' ys' rule: list_assn.induct)
  apply auto
  done
  
thm map_cong



fun prod_assn (infixr "\<times>\<^sub>a" 80) where
  "prod_assn A B (a,b) (ai,bi) = A a ai * B b bi"

  
lemma prod_assn_cong[fundef_cong]:
  "\<lbrakk> p=p'; pi=pi'; A (fst p) (fst pi) = A' (fst p) (fst pi); B (snd p)
(snd pi) = B' (snd p) (snd pi) \<rbrakk> 
    \<Longrightarrow> (A\<times>\<^sub>aB) p pi = (A'\<times>\<^sub>aB') p' pi'" 
    apply (cases p; cases pi)
    by auto
  
  
abbreviation "id_assn x y \<equiv> \<up>(x=y)"

    
fun R where
"R None Leaf = emp" |
"R (Some a) (Node ts t) = 
 (\<exists>\<^sub>A tsi ti xsi. 
      a \<mapsto>\<^sub>r Btnode tsi ti 
    * R ti t 
    * tsi \<mapsto>\<^sub>a xsi
    * list_assn (R \<times>\<^sub>a id_assn) xsi ts
    )" |
"R _ _ = false"


end