theory BTree_Map
imports BTree_Set
begin

term "(1,2)"
term int

fun eq_kv where
"eq_kv (k1, v1) (k2,v2) = (k1 = k2)"

datatype ('a, 'b) ukv = KV 'a 'b

quotient_type ('a,'b) kv  =  "('a, 'b) prod" / eq_kv
  apply(rule equivpI)
    apply (auto simp add: reflp_def symp_def transp_def)
  done

type_notation (ASCII)
  kv  (infixr "\<mapsto>" 20)

instantiation  kv :: (linorder, type) linorder
begin

fun less_eq_ukv::"'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where "less_eq_ukv (k1, v1) (k2, v2) = (k1 \<le> k2)"

lift_definition less_eq_kv :: "'a \<mapsto> 'b \<Rightarrow> 'a \<mapsto> 'b \<Rightarrow> bool" is less_eq_ukv
  by auto

definition less_kv:: "'a \<mapsto> 'b \<Rightarrow> 'a \<mapsto> 'b \<Rightarrow> bool"
  where "less_kv a b = (a \<le> b \<and> \<not>b \<le> a)"


instance
proof(standard, goal_cases)
  case (1 x y)
  then show ?case by (simp add: less_kv_def)
next
  case (2 x)
  then show ?case unfolding less_eq_kv_def
    sorry
next
  case (3 x y z)
  then show ?case sorry
next
  case (4 x y)
  then show ?case sorry
next
  case (5 x y)
  then show ?case sorry
qed
end