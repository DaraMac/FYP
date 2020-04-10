section \<open>Toroidal Elementary Cellular Automata\<close>
(*reference damien's cylinders for these *)

theory Toroidal_Elementary_CA
  imports Finite_Elementary_CA_Base
begin


fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = ((Nb (last xs) x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) x]"


fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open> Basic CA Rule Examples \<close>

definition rule110 :: CA where
"rule110 \<equiv> CA [Zero, One, Zero] r110"
end
