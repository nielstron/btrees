theory BTree                 
  imports Main
begin

text "General structure:  nat values in the leafs and nat/tree node internal node list (nat always larger than every element in the corresponding subtree)"

datatype btree_node = LNode "nat list" | INode "(nat * btree_node) list"

fun btree_set:: "btree_node \<Rightarrow> nat set" where 
  "btree_set (LNode xs) = set xs" |
  "btree_set (INode xs) = (\<Union> (set (map (btree_set \<circ> snd) xs)))"

fun btree_list:: "(nat * btree_node) list \<Rightarrow> bool" where
 "btree_list [] = True" |
 "btree_list ((key, subt)#xs) = (\<forall>x \<in> btree_set subt. x < key \<and> btree_list xs )"

fun all_true where "all_true [] = True" | "all_true (x#xs) = (x \<and> (all_true xs))"

definition "length_invar k xs = (length xs \<ge> k \<and> length xs \<le> 2*k+1)"
definition "key_invar xs = (sorted xs)"

fun btree:: "nat \<Rightarrow> btree_node \<Rightarrow> bool"  where
 "btree k (LNode xs) = (length_invar k xs \<and> key_invar xs)"
| "btree k (INode xs) = (length_invar k xs \<and> key_invar (map fst xs) \<and> btree_list xs \<and> (all_true (map (btree k \<circ> snd) xs)))"

fun btree_list_choose where
"btree_list_choose x [] = None" |
"btree_list_choose x ((key, subt)#xs) = (if key > x then Some subt else btree_list_choose x xs)"

fun height:: "btree_node \<Rightarrow> nat" where
"height (LNode xs) = 0" |
"height (INode xs) = 1 + (Max (set (map height (map snd xs))))"

fun children where
"children (LNode xs) = {}" |
"children (INode xs) = (set (map snd xs))"

lemma children_height: "\<forall>subt \<in> children t. height subt < height t"
proof (induction t)
  case (INode x2)
  show "\<forall>subt\<in>children (INode x2). height subt < height (INode x2)"
  proof
    fix s
    assume "s \<in> children (INode x2)"
    then have "height s \<in> (set (map height (map snd x2)))"
      by auto
    then have "height s \<le> Max (set (map height (map snd x2)))" by auto
    then have "height s < 1 +  Max (set (map height (map snd x2)))" by auto
    then show "height s < height (INode x2)" by auto
  qed    
qed auto

lemma btree_choose_set: "btree_list_choose x xs = t \<Longrightarrow> case t of Some s \<Rightarrow> s \<in> set (map snd xs) | None \<Rightarrow> True"
  apply(induction x xs rule: btree_list_choose.induct)
   apply(auto split: option.splits)
  by (metis list.set_map option.inject option.simps(5))  

lemma btree_choose_children: "btree_list_choose x xs = Some s \<Longrightarrow> s \<in> children (INode xs)"
  using btree_choose_set by fastforce

function (sequential) btree_find where
 "btree_find x (LNode xs) = (if x \<in> set xs then Some x else None)" |
 "btree_find x (INode xs) = (
  case btree_list_choose x xs of
     None \<Rightarrow> None |
     Some subt \<Rightarrow> btree_find x subt
)"
by pat_completeness auto
  termination
    apply (relation "measure (%(a,t). height t)") 
     apply(simp)
    using btree_choose_children
    by (metis case_prod_conv children_height in_measure)

end