section \<open>Toroidal 2D Cellular Automata\<close>

theory Toroidal_TwoDim_CA
  imports Finite_TwoDim_CA_Base
begin

fun get_cell :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> cell" where
"get_cell s x y = s!(nat x)!(nat y)"

fun get_nbhd :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> neighbourhood" where
"get_nbhd s x y = (let w = int_width s in (let h = int_height s in
 list_to_nb [get_cell s ((x+i) mod w) ((y+j) mod h). j \<leftarrow> rev [-1..1], i \<leftarrow> [-1..1]]))"

fun nbhds :: "state \<Rightarrow> neighbourhood list list" where
"nbhds s = (let h = (int_height s)-1 in (let w = (int_width s)-1 in
 [[get_nbhd s x y. y \<leftarrow> [0..h]]. x \<leftarrow> [0..w]]))"

 
fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map (\<lambda> xs. map r xs) (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"
end
