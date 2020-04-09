theory Finite_TwoDim_CA_Base
  imports TwoDim_CA_Base
begin

type_synonym state = "cell list list"

datatype CA = CA (State : state) (Rule : rule)

definition width :: "state \<Rightarrow> nat" where
"width s \<equiv> length s"

definition height :: "state \<Rightarrow> nat" where
"height s = length (hd s)"


value "[(x, y). x \<leftarrow> [0..<10], y \<leftarrow> [0..<10]]"

fun inner_nbhds :: "state \<Rightarrow> neighbourhood list" where
"inner_nbhds (x#y#z#[]) = (Nb x y z) # []" |
"inner_nbhds (x#y#z#zs) = (Nb x y z) # (inner_nbhds (y#z#zs))" |
"inner_nbhds _ = []" (* neighbourhoods aren't defined for \<le> 2 *)

fun get_cell :: "state \<Rightarrow> (nat\<times>nat) \<Rightarrow> cell" where
"get_cell s (x,y) = s!x!y"


value "[(nat (1+i) mod 3, nat (1+j) mod 3). j\<leftarrow>rev [-1..1], i\<leftarrow>[-1..1]]"

fun get_nbhd :: "state \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> neighbourhood" where
"get_nbhd s x y = (let w = width s in list_to_nb )"

fun nbhds :: "state \<Rightarrow> neighbourhood list list" where
"nbhds s = [[get_nbhd s x y. y \<leftarrow> [0..<height ca]]. x \<leftarrow> [0..<width s]]"

fun nbhd :: "state \<Rightarrow> neighbourhood list" where
"nbhd [] = []" | (*this should never happen*)
"nbhd (x#xs) = ((Nb (last xs) x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) x]"


fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"


subsection \<open>Simple properties for CA\<close>

definition widthCA :: "CA \<Rightarrow> nat" where
"widthCA ca = width (State ca)"

definition heightCA :: "CA \<Rightarrow> nat" where
"heightCA ca = height (State ca)"

definition wellformed :: "CA \<Rightarrow> bool" where
"wellformed ca \<equiv> (width ca \<ge> 3) \<and> (height ca \<ge> 3) \<and> (\<forall> i. length ((State ca) ! (i mod (width ca))) = height ca)"

(* doesnt work for 2D currently *)
definition uniform :: "state \<Rightarrow> bool" where
"uniform s \<equiv> length (remdups s) = 1"
end