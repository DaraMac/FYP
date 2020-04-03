(*reference damien's cylinders for these *)

theory ToroidalElementaryCellular
  imports Main CellularBase
begin

section \<open>Basic definitions of Toroidal Elementary Cellular Automata\<close>

fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = ((Nb (last xs) x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) x]"


fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open>Important Property Definitions\<close>

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

(* maybe add some infix notation for this or other things as it looks good *)
fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. State (update_CA (CA s0 r)) = s))"

lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"
  by (metis garden_of_eden.elims(2) reversible.simps)


subsection \<open> Basic Rule Examples \<close>

definition rule110 :: CA where
"rule110 \<equiv> CA [Zero, One, Zero] r110"
end