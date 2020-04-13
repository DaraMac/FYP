section \<open>Bounded 2D Cellular Automata\<close>

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


value "(nbhds offCentre)!1!1"
 
fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map (\<lambda> xs. map r xs) (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open>Properties\<close>

definition stable :: "CA \<Rightarrow> bool" where
"stable ca \<equiv> State (update_CA ca) = State ca"

definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> length (remdups (concat s)) = 1"

definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ r) = (\<forall>s. (\<exists>!s0. State (update_CA (CA s0 r)) = s))"

fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s r) = (\<not>(\<exists> s0. State (update_CA (CA s0 r)) = s))"

lemma "garden_of_eden ca \<Longrightarrow> \<not>reversible ca"
  by (metis garden_of_eden.elims(2) reversible.simps)


definition class1 :: "rule \<Rightarrow> bool" where
"class1 r \<equiv> (\<exists>! f. (\<forall> s. (CA s r) yields f \<and> uniform f \<and> stable (CA f r)))"

definition class2 :: "rule \<Rightarrow> bool" where
"class2 r \<equiv> (\<forall> s. (\<exists> f. (CA s r) yields f \<and> loops (CA f r)))"

lemma "class1 ca \<Longrightarrow> class2 ca"
  using class1_def class2_def loops_def by auto
end
