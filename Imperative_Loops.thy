theory Imperative_Loops
  imports 
    "Separation_Logic_Imperative_HOL.Sep_Main"
    "Refine_Imperative_HOL.Sepref_HOL_Bindings"
    "Refine_Imperative_HOL.Pf_Mono_Prover"
    "Refine_Imperative_HOL.Pf_Add"
    "Refine_Imperative_HOL.Sepref_Basic"
    "Automatic_Refinement.Refine_Lib"
    Instantiate_Existentials
begin

subsection \<open>List-Assn\<close>



lemma list_assn_cong[fundef_cong]:
  "\<lbrakk> xs=xs'; ys=ys'; \<And>x y. \<lbrakk> x\<in>set xs; y\<in>set ys \<rbrakk> \<Longrightarrow> A x y = A' x y \<rbrakk> \<Longrightarrow> list_assn A xs ys = list_assn A' xs' ys'"
  apply (induction xs ys arbitrary: xs' ys' rule: list_assn.induct)
     apply auto
  done

lemma list_assn_aux_simps[simp]:
  "list_assn P [] l' = (\<up>(l'=[]))"
  "list_assn P l [] = (\<up>(l=[]))"
   apply (cases l')
    apply simp
   apply simp
  apply (cases l)
   apply simp
  apply simp
  done

lemma list_assn_aux_append[simp]:
  "length l1=length l1' \<Longrightarrow> 
    list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (induct rule: list_induct2)
   apply simp
  apply (simp add: star_assoc)
  done

lemma list_assn_app_one: "list_assn P (l1@[x]) (l1'@[y]) = list_assn P l1 l1' * P x y"
  apply(induct P l1 l1' rule: list_assn.induct)
     apply (auto simp add: star_assoc)
  done

lemma list_assn_aux_ineq_len: "length l \<noteq> length li \<Longrightarrow> list_assn A l li = false"
proof (induction l arbitrary: li)
  case (Cons x l li) thus ?case by (cases li; auto)
qed simp

lemma list_assn_aux_append2[simp]:
  assumes "length l2=length l2'"  
  shows "list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (cases "length l1 = length l1'")
   apply (erule list_assn_aux_append)
  apply (simp add: list_assn_aux_ineq_len assms)
  done

(* ------------------ ADDED in course of btree_imp -------- *)


lemma list_assn_len: "h \<Turnstile> list_assn A xs ys \<Longrightarrow> length xs = length ys"
  using list_assn_aux_ineq_len by fastforce

lemma list_assn_Cons_left: "list_assn A (x#xs) zs = (\<exists>\<^sub>A z zzs. A x z * list_assn A xs zzs * \<up>(zs = z#zzs))"
  apply(cases zs)
   apply(auto intro!: ent_iffI ent_ex_postI ent_ex_preI)
  done


lemma list_assn_append_left: "list_assn A (xs@ys) zs = (\<exists>\<^sub>A zs1 zs2. list_assn A xs zs1 * list_assn A ys zs2 * \<up>(zs = zs1@zs2))"
  apply(induction xs arbitrary: zs)
   apply(sep_auto simp add: list_assn_Cons_left intro!: ent_iffI)
  apply(sep_auto simp add: list_assn_Cons_left intro!: ent_iffI)
  done


lemma list_assn_append_Cons_left: "list_assn A (xs@x#ys) zs = (\<exists>\<^sub>A zs1 z zs2. list_assn A xs zs1 * A x z * list_assn A ys zs2 * \<up>(zs = zs1@z#zs2))"
  apply (sep_auto simp add: list_assn_Cons_left list_assn_append_left intro!: ent_iffI)
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

subsubsection "Imperative Version of nfoldli"
text \<open>We define an imperative version of \<open>nfoldli\<close>. It is the
  equivalent to the monadic version in the nres-monad\<close>

definition "imp_nfoldli l c f s \<equiv> heap.fixp_fun (\<lambda>D (l,s). case l of 
    [] \<Rightarrow> return s
  | x#ls \<Rightarrow> do {
      b\<leftarrow>c s;
      if b then do { s'\<leftarrow>f x s; D (ls,s')} else return s
    }
  ) (l,s)"

declare imp_nfoldli_def[code del]

lemma imp_nfoldli_simps[simp,code]:
  "imp_nfoldli [] c f s = return s"
  "imp_nfoldli (x#ls) c f s = (do {
    b \<leftarrow> c s;
    if b then do { 
      s'\<leftarrow>f x s; 
      imp_nfoldli ls c f s'
    } else return s
  })"
   apply -
  unfolding imp_nfoldli_def
   apply (subst heap.mono_body_fixp)
    apply pf_mono
   apply simp
  apply (subst heap.mono_body_fixp)
   apply pf_mono
  apply simp
  done

lemma heap_fixp_mono[partial_function_mono]:
  assumes [partial_function_mono]: 
    "\<And>x d. mono_Heap (\<lambda>xa. B x xa d)"
    "\<And>Z xa. mono_Heap (\<lambda>a. B a Z xa)" 
  shows "mono_Heap (\<lambda>x. heap.fixp_fun (\<lambda>D \<sigma>. B x D \<sigma>) \<sigma>)"
  apply rule
  apply (rule ccpo.fixp_mono[OF heap.ccpo, THEN fun_ordD])
    apply (rule mono_fun_fun_cnv, erule thin_rl, pf_mono)+
  apply (rule fun_ordI)
  apply (erule monotoneD[of "fun_ord Heap_ord" Heap_ord, rotated])
  apply pf_mono
  done

lemma imp_nfoldli_mono[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>x \<sigma>. mono_Heap (\<lambda>fa. f fa x \<sigma>)"
  shows "mono_Heap (\<lambda>x. imp_nfoldli l c (f x) \<sigma>)"
  unfolding imp_nfoldli_def
  by pf_mono


subsection \<open>For Loops\<close>




partial_function (heap) imp_for :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for i u c f s = (if i \<ge> u then return s else do {ctn <- c s; if ctn then f i s \<bind> imp_for (i + 1) u c f else return s})"

declare imp_for.simps[code]

lemma [simp]:
  "i \<ge> u \<Longrightarrow> imp_for i u c f s = return s"
  "i < u \<Longrightarrow> imp_for i u c f s = do {ctn <- c s; if ctn then f i s \<bind> imp_for (i + 1) u c f else return s}"
  by (auto simp: imp_for.simps)

lemma imp_nfoldli_deforest:
  "imp_nfoldli [l..<u] c = imp_for l u c"
  apply (intro ext)
  subgoal for f s
    apply (induction "u - l" arbitrary: l u s)
     apply (simp add: upt_conv_Cons; fail)
    apply (simp add: upt_conv_Cons)
    apply (fo_rule arg_cong)
    by (auto cong: if_cong)
  done

partial_function (heap) imp_for' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for' i u f s = (if i \<ge> u then return s else f i s \<bind> imp_for' (i + 1) u f)"

declare imp_for'.simps[code]

lemma [simp]:
  "i \<ge> u \<Longrightarrow> imp_for' i u f s = return s"
  "i < u \<Longrightarrow> imp_for' i u f s = f i s \<bind> imp_for' (i + 1) u f"
  by (auto simp: imp_for'.simps)

lemma imp_for_imp_for':
  "imp_for i u (\<lambda> _. return True) = imp_for' i u"
  apply (intro ext)
  subgoal for f s
    apply (induction "u - i" arbitrary: i u s)
     apply (simp; fail)
    apply simp
    apply (fo_rule arg_cong)
    by auto
  done

partial_function (heap) imp_for_down :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for_down l i c f s = do {
    let i = i - 1;
    ctn \<leftarrow> c s;
    if ctn then do {
      s \<leftarrow> f i s;
      if i>l then imp_for_down l i c f s else return s
    } else return s
  }"  

declare imp_for_down.simps[code]

lemma imp_nfoldli_deforest_down:
  "imp_nfoldli (rev [l..<u]) c = 
    (\<lambda>f s. if u\<le>l then return s else imp_for_down l u c f s)"
proof (intro ext)
  fix f s
  show "imp_nfoldli (rev [l..<u]) c f s =
          (if l \<ge> u then return s else imp_for_down l u c f s)"
  proof cases
    assume "l\<ge>u" thus ?thesis by auto
  next
    assume "\<not>(l\<ge>u)" hence "l<u" by auto
    thus ?thesis 
      apply simp
    proof (induction "u - l" arbitrary: u s)
      case 0 thus ?case by auto
    next
      case (Suc u')
      from Suc.prems Suc.hyps(2) have [simp]: "rev [l..<u] = (u-1)#rev [l..<u-1]"
        apply simp
        apply (subst upt_Suc_append[symmetric])
         apply auto
        done
      show ?case using Suc.hyps(1)[of "u-1"] Suc.hyps(2) Suc.prems
        apply (subst imp_for_down.simps)
        apply (cases "l < u - Suc 0")
         apply (auto simp: Let_def cong: if_cong)
        done
    qed    
  qed  
qed            

context begin

private fun imp_for_down_induction_scheme :: "nat \<Rightarrow> nat \<Rightarrow> unit" where
  "imp_for_down_induction_scheme l i = (
    let i=i-1 in 
    if i>l then 
      imp_for_down_induction_scheme l i
    else ()  
  )"

partial_function (heap) imp_for_down' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for_down' l i f s = do {
    let i = i - 1;
    s \<leftarrow> f i s;
    if i>l then imp_for_down' l i f s else return s
  }"  
declare imp_for_down'.simps[code]

lemma imp_for_down_no_cond:
  "imp_for_down l u (\<lambda>_. return True) = imp_for_down' l u"
  apply (induction l u rule: imp_for_down_induction_scheme.induct)
  apply (intro ext)
  apply (subst imp_for_down.simps)
  apply (subst imp_for_down'.simps)
  apply (simp cong: if_cong)
  done

end

(* TODO: Move. Add rule for imp_for! *)    
lemma imp_for'_rule:
  assumes LESS: "l\<le>u"
  assumes PRE: "P \<Longrightarrow>\<^sub>A I l s"
  assumes STEP: "\<And>i s. \<lbrakk> l\<le>i; i<u \<rbrakk> \<Longrightarrow> <I i s> f i s <I (i+1)>"
  shows "<P> imp_for' l u f s <I u>"
  apply (rule Hoare_Triple.cons_pre_rule[OF PRE])  
  using LESS 
proof (induction arbitrary: s rule: inc_induct)  
  case base thus ?case by sep_auto  
next
  case (step k)
  show ?case using step.hyps 
    by (sep_auto heap: STEP step.IH)  
qed 


text \<open>This lemma is used to manually convert a fold to a loop over indices. \<close>
lemma fold_idx_conv: "fold f l s = fold (\<lambda>i. f (l!i)) [0..<length l] s"
proof (induction l arbitrary: s rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x l) 
  { fix x s
    have "fold (\<lambda>a. f ((l @ [x]) ! a)) [0..<length l] s = fold (\<lambda>a. f (l ! a)) [0..<length l] s"
      by (rule fold_cong) (simp_all add: nth_append)
  } 
  with snoc show ?case by simp
qed    




section \<open>Additional proof rules for typical looping constructs\<close>

subsection \<open>@{term Heap_Monad.fold_map}\<close>

lemma fold_map_ht:
  assumes "list_all (\<lambda>x. <A * true> f x <\<lambda>r. \<up>(Q x r) * A>\<^sub>t) xs"
  shows "<A * true> Heap_Monad.fold_map f xs <\<lambda>rs. \<up>(list_all2 (\<lambda>x r. Q x r) xs rs) * A>\<^sub>t"
  using assms by (induction xs; sep_auto)

lemma fold_map_ht':
  assumes "list_all (\<lambda>x. <true> f x <\<lambda>r. \<up>(Q x r)>\<^sub>t) xs"
  shows "<true> Heap_Monad.fold_map f xs <\<lambda>rs. \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  using assms by (induction xs; sep_auto)

lemma fold_map_ht1:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * \<up>(Q x r)>\<^sub>t"
  shows "
  <A * list_assn R xs xsi * true>
    Heap_Monad.fold_map f xsi
  <\<lambda>rs. A * \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    by (cases xsi; sep_auto heap: assms)
  done

lemma fold_map_ht2:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * R x xi * \<up>(Q x r)>\<^sub>t"
  shows "
  <A * list_assn R xs xsi * true>
    Heap_Monad.fold_map f xsi
  <\<lambda>rs. A * list_assn R xs xsi * \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    apply (cases xsi; sep_auto heap: assms)
     apply (rule cons_rule[rotated 2], rule frame_rule, rprems)
      apply frame_inference
     apply frame_inference
    apply sep_auto
    done
  done

lemma fold_map_ht3:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * Q x r>\<^sub>t"
  shows "<A * list_assn R xs xsi * true> Heap_Monad.fold_map f xsi <\<lambda>rs. A * list_assn Q xs rs>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    apply (cases xsi; sep_auto heap: assms)
     apply (rule Hoare_Triple.cons_pre_rule[rotated], rule frame_rule, rprems, frame_inference)
    apply sep_auto
    done
  done


subsection \<open>@{term imp_for'} and @{term imp_for}\<close>


lemma imp_for'_rule':
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. i < j \<Longrightarrow> <A * I i a * true> f i a <\<lambda>r. A * I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<A * true> imp_for' i j f a <\<lambda>r. A * Q r>\<^sub>t"
proof -
  have "<A * I i a * true> imp_for' i j f a <\<lambda>r. A * I j r>\<^sub>t"
    using \<open>i \<le> j\<close> assms(2)  by (induction "j - i" arbitrary: i a; sep_auto) (rprems, sep_auto+)
  then show ?thesis
    apply (rule cons_rule[rotated 2])
    subgoal
      apply (subst merge_true_star[symmetric])
      apply (rule ent_frame_fwd[OF assms(1)])
       apply frame_inference+
      done
    subgoal
      by (rule ent_frame_fwd[OF assms(3)]) frame_inference+
    done
qed

lemma imp_for_rule:
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. <A * I i a * true> ci a <\<lambda>r. A * I i a * \<up>(r \<longleftrightarrow> c a)>\<^sub>t"
    "\<And>i a. i < j \<Longrightarrow> c a \<Longrightarrow> <A * I i a * true> f i a <\<lambda>r. A * I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a" "\<And>i a. i < j \<Longrightarrow> \<not> c a \<Longrightarrow> I i a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<A * true> imp_for i j ci f a <\<lambda>r. A * Q r>\<^sub>t"
proof -
  have
    "<A * I i a * true>
      imp_for i j ci f a
    <\<lambda>r. A * (I j r \<or>\<^sub>A (\<exists>\<^sub>A i'. \<up>(i' < j \<and> \<not> c r) * I i' r))>\<^sub>t"
    using \<open>i \<le> j\<close> assms(2,3)
    apply (induction "j - i" arbitrary: i a; sep_auto)
      apply (rule ent_star_mono, rule ent_star_mono, rule ent_refl, rule ent_disjI1_direct, rule ent_refl)
     apply rprems
    apply sep_auto
      apply (rprems)
       apply sep_auto+
    apply (rule ent_star_mono, rule ent_star_mono, rule ent_refl, rule ent_disjI2')
     apply solve_entails
     apply simp+
    done
  then show ?thesis
    apply (rule cons_rule[rotated 2])
    subgoal
      apply (subst merge_true_star[symmetric])
      apply (rule ent_frame_fwd[OF assms(1)])
       apply frame_inference+
      done
    apply (rule ent_star_mono)
     apply (rule ent_star_mono, rule ent_refl)
     apply (solve_entails eintros: assms(5) assms(4) ent_disjE)+
    done
qed

lemma (* Alternative proof of imp_for'_rule, via imp_for_rule *)
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. i < j \<Longrightarrow> <A * I i a * true> f i a <\<lambda>r. A * I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<A * true> imp_for' i j f a <\<lambda>r. A * Q r>\<^sub>t"
  unfolding imp_for_imp_for'[symmetric] using assms(3,4)
  by (sep_auto heap: assms imp_for_rule[where c = "\<lambda>_. True"])

(*  
lemma imp_for'_list_all2:
  assumes
    "is_pure R" "n \<le> length xs" "n \<le> length ys"
    "\<And>x xi y yi. <A * R x xi * R y yi * true> Pi xi yi <\<lambda>r. A * \<up> (P x y)>\<^sub>t"
  shows "
  <A * array_assn R xs a  * array_assn R ys b * true>
    imp_for' 0 n
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Pi x y
    })
    True
  <\<lambda>rs. A *  array_assn R xs a  * array_assn R ys b * \<up>(list_all2 P (take n xs) (take n ys))>\<^sub>t"
  apply (rule imp_for'_rule[where I = "\<lambda> i a. \<up> (list_all2 P (take i xs) (take i ys))"])
     apply (sep_auto; fail)
    supply nth_rule =
    sepref_fr_rules(160)[unfolded hn_refine_def hn_ctxt_def, simplified, OF \<open>is_pure R\<close>]
  subgoal for i _
    supply [simp] = pure_def
    using assms(2,3)
    apply sep_auto
     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of i xs])
       apply (simp; fail)
      apply (simp, frame_inference; fail)
     apply frame_inference
    apply sep_auto

     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of i ys])
    unfolding pure_def
       apply (simp; fail)
      apply (simp, frame_inference; fail)
     apply frame_inference
    apply sep_auto

    supply [sep_heap_rules] = assms(4)
    apply sep_auto
    subgoal
      unfolding list_all2_conv_all_nth apply clarsimp
      subgoal for i'
        by (cases "i' = i") auto
      done
    apply frame_inference
    done
   apply auto
  done
*)

lemma imp_nfoldli_rule:
  assumes
    "P \<Longrightarrow>\<^sub>A I [] xs s"
    "\<And>xs ys s. <I xs ys s * true> ci s <\<lambda>r. I xs ys s * \<up>(r \<longleftrightarrow> c s)>\<^sub>t"
    "\<And>as x bs s. xs = as @ x # bs \<Longrightarrow> c s \<Longrightarrow> <I as (x # bs) s * true> f x s <\<lambda>r. I (as @ [x]) bs r>\<^sub>t"
    "\<And>s. I xs [] s \<Longrightarrow>\<^sub>A Q s" "\<And>ys zs s. xs = ys @ zs \<Longrightarrow> \<not> c s \<Longrightarrow> I ys zs s \<Longrightarrow>\<^sub>A Q s"
  shows "<P * true> imp_nfoldli xs ci f s <Q>\<^sub>t"
proof -
  have "
    <I as bs s * true>
      imp_nfoldli bs ci f s
    <\<lambda>r. I (as @ bs) [] r \<or>\<^sub>A (\<exists>\<^sub>A ys zs. \<up>(bs = ys @ zs \<and> \<not> c r) * I (as @ ys) zs r)>\<^sub>t"
    if "xs = as @ bs"
    for as bs s
    using that
    apply (induction bs arbitrary: s as)
     apply (sep_auto, rule ent_star_mono, rule ent_disjI1_direct, rule ent_refl; fail)
    apply simp
    apply sep_auto
     apply (rule assms(2))
    apply sep_auto
      apply (rule assms(3))
       apply assumption+
     apply (rule cons_post_rule, rprems)
      apply (simp; fail)
     apply (sep_auto eintros del: exI)
    subgoal for a bs s as x xb ys zs
      apply (inst_existentials "a # ys" zs)
      apply sep_auto+
      done
    apply (sep_auto eintros del: exI)
    subgoal for a bs s as x
      apply (inst_existentials "[] :: 'a list" "a # bs")
      apply (sep_auto eintros: ent_disjI2_direct ent_star_mono)
      done
    done
  then show ?thesis
    apply (rule cons_rule[rotated 2])
      apply simp
    subgoal
      apply (rule ent_frame_fwd[OF assms(1)])
       apply solve_entails+
      done
    apply (rule ent_star_mono)
     apply (rule ent_disjE, simp, rule assms(4))
     apply (solve_entails eintros: assms(5))
    apply simp
    done
qed




lemma heap_WHILET_rule:
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s"
    "\<And>s. <I s * true> bi s <\<lambda>r. I s * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>s. b s \<Longrightarrow> <I s * true> f s <\<lambda>s'. I s' * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>s. \<not> b s \<Longrightarrow> I s \<Longrightarrow>\<^sub>A Q s"
  shows "<P * true> heap_WHILET bi f s <Q>\<^sub>t"
proof -
  have "<I s * true> heap_WHILET bi f s <\<lambda>s'. I s' * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary:)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3,4) less)
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_star_mono assms(2) ent_refl)
    apply clarsimp
    apply (intro ent_star_mono assms(5) ent_refl)
    .
qed


lemma heap_WHILET_rule':
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s si * F"
    "\<And>si s. <I s si * F> bi si <\<lambda>r. I s si * F * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>si s. b s \<Longrightarrow> <I s si * F> f si <\<lambda>si'. \<exists>\<^sub>As'. I s' si' * F * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>si s. \<not> b s \<Longrightarrow> I s si * F \<Longrightarrow>\<^sub>A Q s si"
  shows "<P> heap_WHILET bi f si <\<lambda>si. \<exists>\<^sub>As. Q s si>\<^sub>t"
proof -
  have "<I s si * F> heap_WHILET bi f si <\<lambda>si'. \<exists>\<^sub>As'. I s' si' * F * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary: si)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        apply (subst heap_WHILET_unfold)
        apply (sep_auto heap: assms(3,4) less)
        done
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_star_mono assms(2) ent_refl)
    apply clarsimp
    apply (sep_auto )
    apply (erule ent_frame_fwd[OF assms(5)])
     apply frame_inference
    by sep_auto

qed

(* Added by NM *)

lemma heap_WHILET_rule'':
  assumes
    "wf R"
    "P \<Longrightarrow>\<^sub>A I s"
    "\<And>s. <I s * true> bi s <\<lambda>r. I s * \<up>(r \<longleftrightarrow> b s)>\<^sub>t"
    "\<And>s. b s \<Longrightarrow> <I s * true> f s <\<lambda>s'. I s' * \<up>((s', s) \<in> R)>\<^sub>t"
    "\<And>s. \<not> b s \<Longrightarrow> I s * true \<Longrightarrow>\<^sub>A Q s"
  shows "<P * true> heap_WHILET bi f s <Q>"
proof -
  have "<I s * true> heap_WHILET bi f s <\<lambda>s'. I s' * \<up>(\<not> b s')>\<^sub>t"
    using assms(1)
  proof (induction arbitrary:)
    case (less s)
    show ?case
    proof (cases "b s")
      case True
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3,4) less)
    next
      case False
      then show ?thesis
        by (subst heap_WHILET_unfold) (sep_auto heap: assms(3))
    qed
  qed
  then show ?thesis
    apply (rule cons_rule[rotated 2])
     apply (intro ent_star_mono assms(2) ent_refl)
    apply clarsimp
    apply (intro ent_star_mono assms(5) ent_refl)
    .
qed


end
