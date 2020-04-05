theory InfiniteElementaryCellular
  imports Main
begin

datatype cell = Zero | One

type_synonym state = "int \<Rightarrow> cell"
datatype neighbourhood = Nb cell cell cell
type_synonym rule = "neighbourhood \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

fun update_state :: "CA \<Rightarrow> state" where
"update_state (CA s r) n = r (Nb (s (n-1)) (s n) (s (n+1)))"

fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (update_state (CA s r)) r"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

fun run_t_steps :: "CA \<Rightarrow> nat \<Rightarrow> CA" where
"run_t_steps ca n = apply_t_times update_CA ca n"

fun r110 :: rule where
"r110  (Nb One One One) = Zero"   |
"r110  (Nb One One Zero) = One"   |
"r110  (Nb One Zero One) = One"   |
"r110  (Nb One Zero Zero) = Zero" |
"r110  (Nb Zero One One) = One"   |
"r110  (Nb Zero One Zero) = One"  |
"r110  (Nb Zero Zero One) = One"  |
"r110  (Nb Zero Zero Zero) = Zero"

definition state1 :: state where
"state1 s \<equiv> (if s = 0 then One else Zero)"

definition rule110 :: CA where
"rule110 \<equiv> CA state1 r110"

value "State (run_t_steps rule110 5) (-3)"
end
