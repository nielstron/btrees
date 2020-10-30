theory BTree_Height
  imports BTree Main
begin

section "Maximum and minimum height"

text "Textbooks usually provide some proofs relating the maxmimum and minimum height of the BTree
for a given number of nodes. We therefore introduce this counting and show the respective proofs."


text "The default size function does not suit our needs in this case.
 We would like to count the number of nodes in the tree only, not regarding the number of keys."

(* we want a different counting method,
  namely only the number of nodes in a tree *)
fun size_btree::"'a btree \<Rightarrow> nat" where
"size_btree Leaf = 0" |
"size_btree (Node ts t) = 1 + sum_list (map size_btree (subtrees ts)) + (size_btree t)"

find_theorems "height Leaf"

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


lemma size_height_upper_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> size_btree t * (2*k) \<le> (2*k+1)^(height t) - 1"
proof(induction t rule: size_btree.induct)
  case (2 ts t)
  let ?sub_height = "((2 * k + 1) ^ height t - 1)"
  have "sum_list (map size_btree (subtrees ts)) * (2*k) =
        sum_list (map (\<lambda>t. size_btree t * (2 * k)) (subtrees ts))"
    using sum_list_distrib[of size_btree "subtrees ts" "2*k"] by simp
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

(* maximum number of nodes *)
subsection "Maximum height for a given number of nodes"

lemma size_height_lower_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> ((k+1)^(height t) - 1) \<le> size_btree t * k"
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

(* TODO results for root_order/bal *)
text "Since BTrees have special roots, we need to show the overall size seperately"

lemma size_root_height_lower_bound:
  assumes "root_order k t"
    and "bal t"
  shows "2*((k+1)^(height t - 1) - 1) \<le> size_btree t * k"
proof (cases t)
case Leaf
  then show ?thesis by simp
next
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
qed

end