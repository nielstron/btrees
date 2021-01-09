theory BTree_Height
  imports BTree Main
begin

section "Maximum and minimum height"

text "Textbooks usually provide some proofs relating the maxmimum and minimum height of the BTree
for a given number of nodes. We therefore introduce this counting and show the respective proofs."



text "The default size function does not suit our needs.
 We would like to count the number of nodes in the tree only, not regarding the number of keys."

(* we want a different counting method,
  namely only the number of nodes in a tree *)
fun size_btree::"'a btree \<Rightarrow> nat" where
  "size_btree Leaf = 0" |
  "size_btree (Node ts t) = 1 + sum_list (map size_btree (subtrees ts)) + (size_btree t)"


(* maximum number of nodes for given height *)
subsection "Maximum number of nodes for a given height"


lemma sum_list_replicate: "sum_list (replicate n c) = n*c"
  apply(induction n)
   apply(auto simp add: ring_class.ring_distribs(2))
  done

lemma sum_list_distrib: "sum_list (map f xs) * (c::nat) = sum_list (map (\<lambda>x. f x * c) xs)"
  apply(induction xs)
   apply(auto simp add: add_mult_distrib)
  done

abbreviation "upper_bound k h \<equiv> (2*k+1)^h - 1"

lemma size_height_upper_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> size_btree t * (2*k) \<le> upper_bound k (height t)"
proof(induction t rule: size_btree.induct)
  case (2 ts t)
  let ?sub_height = "((2 * k + 1) ^ height t - 1)"
  have "sum_list (map size_btree (subtrees ts)) * (2*k) =
        sum_list (map (\<lambda>t. size_btree t * (2 * k)) (subtrees ts))"
    using sum_list_mult_const by metis
  also have "\<dots> \<le> sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using 2 by (simp add: sum_list_mono)
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> = (length ts)*(?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> \<le> (2*k)*(?sub_height)"
    using "2.prems"(1)
    by simp
  finally have "sum_list (map size_btree (subtrees ts))*(2*k) \<le> ?sub_height*(2*k)"
    by simp
  moreover have "(size_btree t)*(2*k) \<le> ?sub_height"
    using 2 by simp
  ultimately have "(size_btree (Node ts t))*(2*k) \<le> 
         2*k
        + ?sub_height * (2*k)
        + ?sub_height"
    unfolding size_btree.simps add_mult_distrib
    by linarith
  also have "\<dots> =  2*k + (2*k)*((2 * k + 1) ^ height t) - 2*k + (2 * k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = (2*k)*((2 * k + 1) ^ height t) + (2 * k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (2*k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?case
    by (metis "2.prems"(2) height_bal_tree)
qed simp

text "To verify our lower bound is sharp, we compare it to the height of artificially constructed
full trees."

fun full_tree::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
  "full_tree k c 0 = Leaf"|
  "full_tree k c (Suc n) = (Node (replicate (2*k) ((full_tree k c n),c)) (full_tree k c n))"

value "let k = (2::nat) in map (\<lambda>x. size_btree x * 2*k) (map (full_tree k (1::nat)) [0,1,2,3,4])"
value "let k = (2::nat) in map (\<lambda>x. ((2*k+(1::nat))^(x)-1)) [0,1,2,3,4]"

lemma compow_comp_id: "c > 0 \<Longrightarrow> f \<circ> f = f \<Longrightarrow> (f ^^ c) = f"
  apply(induction c)
   apply auto
  by fastforce


lemma compow_id_point: "f x = x \<Longrightarrow> (f ^^ c) x = x"
  apply(induction c)
   apply auto
  done


lemma height_full_tree: "height (full_tree k a h) = h"
  apply(induction k a h rule: full_tree.induct)
   apply (auto simp add: compow_id_point)
  done

lemma bal_full_tree: "bal (full_tree k a h)"
  apply(induction k a h rule: full_tree.induct)
   apply auto
  done

lemma order_full_tree: "order k (full_tree k a h)"
  apply(induction k a h rule: full_tree.induct)
   apply auto
  done

lemma full_btrees_sharp: "size_btree (full_tree k a h) * (2*k) = upper_bound k h"
  apply(induction k a h rule: full_tree.induct)
   apply (auto simp add: height_full_tree algebra_simps sum_list_replicate)
  done

lemma upper_bound_sharp:
  "t = full_tree k () h \<Longrightarrow> height t = h \<and> order k t \<and> bal t \<and> upper_bound k h = size_btree t * (2*k)"
  by (simp add: bal_full_tree height_full_tree order_full_tree full_btrees_sharp)


(* maximum number of nodes *)
subsection "Maximum height for a given number of nodes"

abbreviation "lower_bound k h \<equiv> ((k+1)^h - 1)"

lemma size_height_lower_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> lower_bound k (height t) \<le> size_btree t * k"
proof(induction t rule: size_btree.induct)
  case (2 ts t)
  let ?sub_height = "((k + 1) ^ height t - 1)"
  have "k*(?sub_height) \<le> (length ts)*(?sub_height)"
    using "2.prems"(1)
    by simp
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> = sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>t. size_btree t * k) (subtrees ts))"
    using 2 by (simp add: sum_list_mono)
  also have "\<dots> = sum_list (map size_btree (subtrees ts)) * k"
    find_theorems "sum_list _ * _"
    using sum_list_distrib[of size_btree "subtrees ts" k] by simp
  finally have "sum_list (map size_btree (subtrees ts))*k \<ge> ?sub_height*k"
    by simp
  moreover have "(size_btree t)*k \<ge> ?sub_height"
    using 2 by simp
  ultimately have "(size_btree (Node ts t))*k \<ge> 
        k
        + ?sub_height * k
        + ?sub_height"
    unfolding size_btree.simps add_mult_distrib
    by linarith
  also have
    "k + ?sub_height * k + ?sub_height = 
     k + k*((k + 1) ^ height t) - k + (k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = k*((k + 1) ^ height t) + (k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?case
    by (metis "2.prems"(2) height_bal_tree)
qed simp

text "To verify our upper bound is sharp, we compare it to the height of artificially constructed
minimally filled (=slim) trees."

fun slim_tree::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
  "slim_tree k c 0 = Leaf"|
  "slim_tree k c (Suc n) = (Node (replicate k ((slim_tree k c n),c)) (slim_tree k c n))"

value "let k = (2::nat) in map (\<lambda>x. size_btree x * k) (map (slim_tree k (1::nat)) [0,1,2,3,4])"
value "let k = (2::nat) in map (\<lambda>x. ((k+1::nat)^(x)-1)) [0,1,2,3,4]"


lemma height_slim_tree: "height (slim_tree k a h) = h"
  apply(induction k a h rule: slim_tree.induct)
   apply (auto simp add: compow_id_point)
  done

lemma bal_slim_tree: "bal (slim_tree k a h)"
  apply(induction k a h rule: full_tree.induct)
   apply auto
  done

lemma order_slim_tree: "order k (slim_tree k a h)"
  apply(induction k a h rule: full_tree.induct)
   apply auto
  done

lemma slim_trees_sharp: "size_btree (slim_tree k a h) * k = lower_bound k h"
  apply(induction k a h rule: slim_tree.induct)
   apply (auto simp add: height_slim_tree algebra_simps sum_list_replicate compow_id_point)
  done

lemma lower_bound_sharp:
  "t = slim_tree k () h \<Longrightarrow> height t = h \<and> order k t \<and> bal t \<and> lower_bound k h = size_btree t * k"
  by (simp add: bal_slim_tree height_slim_tree order_slim_tree slim_trees_sharp)

(* TODO results for root_order/bal *)
text "Since BTrees have special roots, we need to show the overall size seperately"

lemma size_root_height_lower_bound:
  assumes "root_order k t"
    and "bal t"
  shows "2*((k+1)^(height t - 1) - 1) \<le> size_btree t * k"
proof (cases t)
  case (Node ts t)
  let ?sub_height = "((k + 1) ^ height t - 1)"
  from Node have "?sub_height \<le> length ts * ?sub_height"
    using assms
    by (simp add: Suc_leI)
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using sum_list_replicate
    by simp
  also have "\<dots> = sum_list (map (\<lambda>x. ?sub_height) (subtrees ts))"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>t. size_btree t * k) (subtrees ts))"
    using Node
      sum_list_mono[of "subtrees ts" "\<lambda>x. (k+1)^(height t) - 1" "\<lambda>x. size_btree x * k"]
      size_height_lower_bound assms
    by fastforce
  also have "\<dots> = sum_list (map size_btree (subtrees ts)) * k"
    using sum_list_distrib[of size_btree "subtrees ts" k] by simp
  finally have "sum_list (map size_btree (subtrees ts))*k \<ge> ?sub_height"
    by simp

  moreover have "(size_btree t)*k \<ge> ?sub_height"
    using Node assms size_height_lower_bound
    by auto
  ultimately have "(size_btree (Node ts t))*k \<ge> 
        ?sub_height
        + ?sub_height"
    unfolding size_btree.simps add_mult_distrib
    by linarith
  then show ?thesis
    using Node assms(2) height_bal_tree by fastforce
qed simp

lemma size_root_height_upper_bound: 
  assumes "root_order k t"
    and "bal t"
  shows "size_btree t * (2*k) \<le> (2*k+1)^(height t) - 1"
proof(cases t)
  case (Node ts t)
  let ?sub_height = "((2 * k + 1) ^ height t - 1)"
  have "sum_list (map size_btree (subtrees ts)) * (2*k) =
        sum_list (map (\<lambda>t. size_btree t * (2 * k)) (subtrees ts))"
    using sum_list_mult_const by metis
  also have "\<dots> \<le> sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using Node
      sum_list_mono[of "subtrees ts" "\<lambda>x. size_btree x * (2*k)"  "\<lambda>x. (2*k+1)^(height t) - 1"]
      size_height_upper_bound assms
    by fastforce
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> = (length ts)*(?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> \<le> (2*k)*?sub_height"
    using assms Node
    by simp
  finally have "sum_list (map size_btree (subtrees ts))*(2*k) \<le> ?sub_height*(2*k)"
    by simp
  moreover have "(size_btree t)*(2*k) \<le> ?sub_height"
    using Node assms size_height_upper_bound
    by auto
  ultimately have "(size_btree (Node ts t))*(2*k) \<le> 
         2*k
        + ?sub_height * (2*k)
        + ?sub_height"
    unfolding size_btree.simps add_mult_distrib
    by linarith
  also have "\<dots> =  2*k + (2*k)*((2 * k + 1) ^ height t) - 2*k + (2 * k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = (2*k)*((2 * k + 1) ^ height t) + (2 * k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (2*k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?thesis
    by (metis Node assms(2) height_bal_tree)
qed simp

lemma root_order_imp_divmuleq: "root_order k t \<Longrightarrow> (size_btree t * k) div k = size_btree t"
  using root_order.elims(2) by fastforce

lemma size_root_height_lower_bound_simp:
  assumes "root_order k t"
    and "bal t"
  shows "2*((k+1)^(height t - 1) - 1) div k \<le> size_btree t"
proof -
  have "2*((k+1)^(height t - 1) - 1) div k \<le> (size_btree t * k) div k"
    using size_root_height_lower_bound[OF assms] div_le_mono
    by blast
  also have "\<dots> = size_btree t"
    using root_order_imp_divmuleq[OF assms(1)]
    by simp
  finally show ?thesis .
qed

lemma size_root_height_upper_bound_simp:
  assumes "root_order k t"
    and "bal t"
  shows "size_btree t \<le> ((2*k+1)^(height t) - 1) div (2*k)"
proof -
  have "size_btree t = (size_btree t * (2*k)) div (2*k)"
    using root_order_imp_divmuleq[OF assms(1)]
    by simp
  also have "\<dots> \<le> ((2*k+1)^(height t) - 1) div (2*k)"
    using div_le_mono size_root_height_upper_bound[OF assms] by blast
  finally show ?thesis .
qed



end