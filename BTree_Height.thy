theory BTree_Height
  imports BTree Complex_Main
begin

(* TODO textbook proof about size of a tree = number of nodes *)

find_theorems sum_list
thm Ex_list_of_length
thm map_replicate_const
thm length_map

thm ring_class.ring_distribs

lemma sum_list_replicate: "sum_list (replicate n (c::real)) = n*c"
  apply(induction n)
   apply(auto simp add: ring_class.ring_distribs(2))
  done

lemma sum_list_real: "sum_list (map real xs) = real (sum_list xs)"
  apply(induction xs)
   apply(auto)
  done


(* we want a different counting method,
  namely only the number of nodes in a tree *)
fun size_btree::"'a btree \<Rightarrow> nat" where
"size_btree Leaf = 0" |
"size_btree (Node ts t) = sum_list (map size_btree (subtrees ts)) + (size_btree t) + 1"

find_theorems "height Leaf"

(* maximum number of nodes for given height *)

fun full_tree::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
"full_tree k c 0 = Leaf"|
"full_tree k c (Suc n) = (Node (replicate (2*k) ((full_tree k c n),c)) (full_tree k c n))"

value "size_btree (full_tree 1 (1::nat) 1)"
value "map size_btree (map (full_tree 2 (1::nat)) [0,1,2,3,4])"
value "map (\<lambda>x. ((5::nat)^(x)-1) / 4) [0,1,2,3,4]"

lemma height_ge_zero: "((2 * real k + 1) ^ height t - 1) / (2 * real k) \<ge> 0"
  by simp

lemma mult_right_mono_nat: "\<lbrakk>a \<le> b; c \<ge> 0\<rbrakk> \<Longrightarrow> (a::nat)*(c::real) \<le> (b::nat)*(c::real)"
  by (simp add: mult_right_mono)


lemma size_height_upper_bound: "\<lbrakk>k > 0; order k t; bal t\<rbrakk> \<Longrightarrow> size_btree t \<le> ((2*k+1)^(height t) - 1) / (2*k)"
proof(induction t rule: size_btree.induct)
  case (2 ts t)
  let ?sub_height = "((2 * real k + 1) ^ height t - 1) / (2 * real k)" and ?sub_height_mul2k = "((2 * real k + 1) ^ height t - 1)"
  from 2 have "sum_list (map (real \<circ> size_btree) (subtrees ts)) \<le> sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    by (simp add: sum_list_mono)
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> = (length ts)*(?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> \<le> (2*k)*(?sub_height)"
    using "2.prems"(2) height_ge_zero mult_right_mono_nat
    by (metis order.simps(2))
  also have "\<dots> = ?sub_height_mul2k"
    by simp
  finally have "real (sum_list (map (size_btree) (subtrees ts))) \<le> ?sub_height_mul2k"
    using sum_list_real
    by (metis map_map)
  moreover have "real (size_btree t) \<le> ?sub_height"
    using 2 by simp
  ultimately have "real (size_btree (Node ts t)) \<le> 
        ?sub_height_mul2k
        + ?sub_height
        + 1"
    unfolding size_btree.simps
    by linarith
  also have "\<dots>  \<le> (2*real k)*?sub_height + ?sub_height + 1"
    by simp
  also have "\<dots> = ((2*real k)*((2 * real k + 1) ^ height t - 1) + (2 * real k + 1) ^ height t - 1) / (2*real k) + 1"
    by (simp add: add_divide_distrib group_cancel.sub1)
  also have "\<dots> = ((2*real k)*((2 * real k + 1) ^ height t) + ((2 * real k + 1) ^ height t) - 1 - (2* real k)) / (2*real k) + 1"
  proof -
    have "\<forall>r ra. (ra::real) * r - ra = ra * (r - 1)"
      by (simp add: right_diff_distrib)
    then show ?thesis
      by auto
  qed
  also have "\<dots> = (((2 * real k + 1) ^ (height t + 1)) - 1 - (2* real k)) / (2*real k) + 1"
    using comm_semiring_1_class.semiring_normalization_rules(2)[of "2*real k" "(2 * real k + 1) ^ height t"] by simp
  also have "\<dots> = (((2 * real k + 1) ^ (height t + 1)) - 1 - (2* real k) + (2* real k)) / (2*real k)"
    by (simp add: "2.prems"(1) diff_divide_distrib)
  also have "\<dots> = (((2 * real k + 1) ^ (height t + 1)) - 1) / (2*real k)"
    by simp
  also have "\<dots> = ((2 * real k + 1) ^ (height (Node ts t)) - 1) / (2*real k)"
    using height_bal_tree "2.prems"(3) by fastforce
  finally show ?case
    by simp
qed simp

(* maximum number of nodes *)

fun slim_tree::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
"slim_tree k c 0 = Leaf"|
"slim_tree k c (Suc n) = (Node (replicate k ((slim_tree k c n),c)) (slim_tree k c n))"

value "size_btree (slim_tree 1 (1::nat) 1)"
value "map size_btree (map (slim_tree 2 (1::nat)) [0,1,2,3,4])"
value "map (\<lambda>x. ((3::nat)^(x)-1) / 2) [0,1,2,3,4]"

lemma size_height_lower_bound: "\<lbrakk>k > 0; order k t; bal t\<rbrakk> \<Longrightarrow> ((k+1)^(height t) - 1) / k \<le> size_btree t"
  sorry

end