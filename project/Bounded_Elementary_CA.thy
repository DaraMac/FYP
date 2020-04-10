(*chapter \<open>Finite Cellular Automata\<close>*)

(*reference damien's cylinders for those *)

theory Bounded_Elementary_CA
  imports Finite_Elementary_CA_Base
begin

section \<open>Basic definitions of Finite Elementary Cellular Automata\<close>
(* Going to go with left/right boundaries as Zero by default *)
(* Might like that to be flexible somehow? Without ruining CA type def*)

(* doesnt need wellformed anymore!*)
fun nbhds :: "state \<Rightarrow> neighbourhood list" where
"nbhds [] = []" | (*this should never happen*)
"nbhds (x#[]) = [(Nb Zero x Zero)]" |
"nbhds (x#y#[]) = [(Nb Zero x y), (Nb x y Zero)]" |
"nbhds (x#xs) = ((Nb Zero x (hd xs)) # (inner_nbhds (x#xs))) @ [Nb (last (butlast xs)) (last xs) Zero]"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"
end
