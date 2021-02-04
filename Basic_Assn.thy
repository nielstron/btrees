theory Basic_Assn
  imports
    "Refine_Imperative_HOL.Sepref_HOL_Bindings"
    "Refine_Imperative_HOL.Sepref_Basic"
begin

(* Auxiliary assertion types and lemmas provided by Peter Lammich *)

subsection \<open>List-Assn\<close>



lemma list_assn_cong[fundef_cong]:
  "\<lbrakk> xs=xs'; ys=ys'; \<And>x y. \<lbrakk> x\<in>set xs; y\<in>set ys \<rbrakk> \<Longrightarrow> A x y = A' x y \<rbrakk> \<Longrightarrow> list_assn A xs ys = list_assn A' xs' ys'"
  apply (induction xs ys arbitrary: xs' ys' rule: list_assn.induct)
     apply auto
  done


lemma list_assn_app_one: "list_assn P (l1@[x]) (l1'@[y]) = list_assn P l1 l1' * P x y"
  by simp



(* ------------------ ADDED by NM in course of btree_imp -------- *)


lemma list_assn_len: "h \<Turnstile> list_assn A xs ys \<Longrightarrow> length xs = length ys"
  using list_assn_aux_ineq_len by fastforce

thm list_assn_aux_cons_conv
lemma list_assn_Cons_left: "list_assn A (x#xs) zs = (\<exists>\<^sub>A z zzs. A x z * list_assn A xs zzs * \<up>(zs = z#zzs))"
  oops

thm list_assn_aux_append_conv1
lemma list_assn_append_left: "list_assn A (xs@ys) zs = (\<exists>\<^sub>A zs1 zs2. list_assn A xs zs1 * list_assn A ys zs2 * \<up>(zs = zs1@zs2))"
  oops


lemma list_assn_append_Cons_left: "list_assn A (xs@x#ys) zs = (\<exists>\<^sub>A zs1 z zs2. list_assn A xs zs1 * A x z * list_assn A ys zs2 * \<up>(zs1@z#zs2 = zs))"
  apply (sep_auto simp add: list_assn_aux_cons_conv list_assn_aux_append_conv1 intro!: ent_iffI)
  done


lemma list_assn_aux_append_Cons: 
  shows "length xs = length zsl \<Longrightarrow> list_assn A (xs@x#ys) (zsl@z#zsr) = (list_assn A xs zsl * A x z * list_assn A ys zsr) "
  by (sep_auto simp add: mult.assoc)


(* -------------------------------------------- *)

subsection \<open>Prod-Assn\<close>


lemma prod_assn_cong[fundef_cong]:
  "\<lbrakk> p=p'; pi=pi'; A (fst p) (fst pi) = A' (fst p) (fst pi); B (snd p) (snd pi) = B' (snd p) (snd pi) \<rbrakk> 
    \<Longrightarrow> (A\<times>\<^sub>aB) p pi = (A'\<times>\<^sub>aB') p' pi'" 
  apply (cases p; cases pi)
  by auto

end