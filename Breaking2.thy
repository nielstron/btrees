theory Breaking2
imports Breaking
begin
context breaking
begin

lemma "node_i k [] t = T_i (Node [] t)"
  apply(simp del: node_i.simps)
  oops
end
end