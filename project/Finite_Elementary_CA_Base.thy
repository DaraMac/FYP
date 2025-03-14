section \<open>Finite Elementary Cellular Automata Base\<close>

theory Finite_Elementary_CA_Base
  imports Elementary_CA_Base
begin

subsection \<open>Basis type of all finite elementary 1D CA\<close>

type_synonym state = "cell list"

datatype CA = CA (State : state) (Rule : rule)

fun inner_nbhds :: "state \<Rightarrow> neighbourhood list" where
"inner_nbhds (x#y#z#[]) = (Nb x y z) # []" |
"inner_nbhds (x#y#z#zs) = (Nb x y z) # (inner_nbhds (y#z#zs))" |
"inner_nbhds _ = []" (* neighbourhoods aren't defined for \<le> 2 *)


subsection \<open>Simple properties for CA\<close>

definition width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"

definition wellformed :: "CA \<Rightarrow> bool" where
"wellformed ca \<equiv> (width ca \<ge> 3)"

(* doesnt hold for empty list *)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> length (remdups s) = 1"
end
