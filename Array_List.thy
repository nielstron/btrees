theory Array_List
  imports
 "Refine_Imperative_HOL.IICF_Array_List"
 "Imperative_Loops"
begin

text "A non-dynamic re-interpretation of array-lists.
The idea is to model arrays that take a certain amount of memory but
are only filled up to a fixed number of elements. Types from IICF can be reused
but we need to show that some theorems hold for weaker constraints."

definition is_array_list where
"is_array_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>A l'. a \<mapsto>\<^sub>a l' *  \<up>(n \<le> length l' \<and> l = (take n l'))"

term arl_get
(* trying to replicate this *)
thm nth_rule
thm arl_get_rule
find_theorems "_!_ = _!_"
lemma arl_get_rule[sep_heap_rules]: "
  i < length xs \<Longrightarrow>
  < a \<mapsto>\<^sub>a xs * \<up>(n \<le> length xs)> 
    arl_get (a,n) i
  <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(n \<le> length xs) * id_assn (xs!i) r>"
  apply (sep_auto simp: arl_get_def  split: prod.split)
  done

lemma arl_get_rule'[sep_heap_rules]: "
  i < n \<Longrightarrow>
  < a \<mapsto>\<^sub>a xs * \<up>(n \<le> length xs)> 
    arl_get (a,n) i
  <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(n \<le> length xs) * id_assn (xs!i) r>"
  apply (sep_auto simp: arl_get_def  split: prod.split)
  done  


fun array_list_assn where
"array_list_assn A l (a,n) =  (\<exists>\<^sub>A l'. 
      a \<mapsto>\<^sub>a l'
    * \<up>(n \<le> length l')
    * list_assn A l (take n l')
    )"


end