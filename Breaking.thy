theory Breaking
imports BTree
begin


fun split_half:: "('a btree\<times>'a) list \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
  "split_half xs = (take (length xs div 2) xs, drop (length xs div 2) xs)"


locale breaking =
  fixes split_fun ::  "(('a::linorder) btree\<times>'a) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)"
  assumes split_fun_req:
    "\<lbrakk>split_fun xs p = (ls,rs)\<rbrakk> \<Longrightarrow> ls @ rs = xs"
    "\<lbrakk>split_fun xs p = (ls@[(sub,sep)],rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> sep < p"
    "\<lbrakk>split_fun xs p = (ls,(sub,sep)#rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> p \<le> sep"
begin


datatype 'b up_i = T_i "'b btree" | Up_i "'b btree" 'b "'b btree"



fun node_i:: "nat \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> 'a btree \<Rightarrow> 'a up_i" where
  "node_i k xs x = (
  if length xs \<le> 2*k then T_i (Node xs x)
  else (
    case split_half xs of (ls, (sub,sep)#rs) \<Rightarrow>
      Up_i (Node ls sub) sep (Node rs x)
    )
  )"

lemma "node_i k [] t = T_i (Node [] t)"
  apply(simp del: node_i.simps)
  oops


interpretation S_ordered: Set_by_Ordered where
  empty = Leaf and
  insert = undefined and 
  delete = undefined and
  isin = undefined   and
  inorder = undefined   and
  inv = undefined
  sorry

end






end