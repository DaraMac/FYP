theory Bounded_TwoDim_CA
  imports Finite_TwoDim_CA_Base
begin

fun out_of_bounds :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"out_of_bounds s x y = (if x \<ge> int_width s \<or> x < 0 \<or> y \<ge> int_height s \<or> y < 0 then True else False)"

fun get_cell :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> cell" where
"get_cell s x y = (if out_of_bounds s x y then Zero else  s!(nat x)!(nat y))"

fun get_nbhd :: "state \<Rightarrow> int \<Rightarrow> int \<Rightarrow> neighbourhood" where
"get_nbhd s x y = list_to_nb [get_cell s (x+i) (y+j). j \<leftarrow> rev [-1..1], i \<leftarrow> [-1..1]]"

fun nbhds :: "state \<Rightarrow> neighbourhood list list" where
"nbhds s = (let h = (int_height s)-1 in (let w = (int_width s)-1 in
 [[get_nbhd s x y. y \<leftarrow> [0..h]]. x \<leftarrow> [0..w]]))"

 
fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map (\<lambda> xs. map r xs) (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"
end