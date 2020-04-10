section \<open>Infinite Elementary Cellular Automata\<close>

theory Infinite_Elementary_CA
  imports Elementary_CA_Base
begin

type_synonym state = "int \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

fun update_state :: "CA \<Rightarrow> state" where
"update_state (CA s r) n = r (Nb (s (n-1)) (s n) (s (n+1)))"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (update_state (CA s r)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open>Example CAs\<close>

definition state1 :: state where
"state1 s \<equiv> (if s = 0 then One else Zero)"

definition rule110 :: CA where
"rule110 \<equiv> CA state1 r110"

value "State (run_t_steps rule110 5) (-3)"
end
