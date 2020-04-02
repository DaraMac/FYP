(*reference damien's cylinders for these *)

theory ToroidalElementaryCellular
  imports Main CellularBase
begin

section \<open>Basic definitions of Toroidal Elementary Cellular Automata\<close>

(* Generate the neighbourhoods for each cell *)
(* this is the only function that needs to change to make different topologies!*)
fun inner_nbhds :: "state \<Rightarrow> neighbourhood list" where
"inner_nbhds (x#y#z#[]) = (Nb x y z) # []" |
"inner_nbhds (x#y#z#zs) = (Nb x y z) # (inner_nbhds (y#z#zs))" |
"inner_nbhds _ = []" (* neighbourhoods aren't defined for \<le> 2 *)

fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#xs) = ((Nb (last xs) x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) x]"


fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"

definition rule110 :: CA where
"rule110 \<equiv> CA [Zero, One, Zero] r110" 

value "State (run_t_steps rule110 5)"
end