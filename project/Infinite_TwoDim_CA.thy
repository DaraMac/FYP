theory Infinite_TwoDim_CA
  imports TwoDim_CA_Base
begin
  
type_synonym state = "int \<Rightarrow> int \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

(*could this be written nicer? maybe a calculate neighbourhood function*)
fun update_state :: "CA \<Rightarrow> state" where
"update_state (CA s r) x y = r (Nb (s (x-1) (y+1)) (s x (y+1)) (s (x+1) (y+1))
                                   (s (x-1)  y)    (s x  y)    (s (x+1)  y)
                                   (s (x-1) (y-1)) (s x (y-1)) (s (x+1) (y-1)))"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (update_state (CA s r)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"
end