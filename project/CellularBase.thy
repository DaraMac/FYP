theory CellularBase
  imports Main
begin

section \<open>Base datatypes and definitions common to all Cellular Automata\<close>
(* Might end up having different bases between 1 and 2D*)
(* perhaps typeclass them so well-formed works on all? *)

subsection \<open>Basis type of all elementary 1D CA\<close>

datatype cell = One | Zero
type_synonym state = "cell list"
datatype neighbourhood = Nb cell cell cell 
type_synonym rule = "neighbourhood \<Rightarrow> cell"

datatype CA = CA (State : state) (Rule : rule)

consts nbhds :: "state \<Rightarrow> neighbourhood list" (* This doesn't really do anything helpful yet *)

(* 1D only *)
fun inner_nbhds :: "state \<Rightarrow> neighbourhood list" where
"inner_nbhds (x#y#z#[]) = (Nb x y z) # []" |
"inner_nbhds (x#y#z#zs) = (Nb x y z) # (inner_nbhds (y#z#zs))" |
"inner_nbhds _ = []" (* neighbourhoods aren't defined for \<le> 2 *)

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"


subsection \<open>Simple properties for CA\<close>

definition width :: "CA \<Rightarrow> nat" where
"width ca = length (State ca)"

(*fun update_CA :: "CA \<Rightarrow> CA" where
"update_CA (CA s r) = CA (map r (nbhds s)) r"*)

definition wellformed :: "CA \<Rightarrow> bool" where
"wellformed ca \<equiv> (width ca \<ge> 3)"

(*definition yields :: "CA \<Rightarrow> state \<Rightarrow> bool" (infixr \<open>yields\<close>  65) where
"A yields s \<equiv> (\<exists> n. State (run_t_steps A n) = s \<and> n > 0)"

definition loops :: "CA \<Rightarrow> bool" where
"loops ca \<equiv> ca yields State ca"

fun garden_of_eden :: "CA \<Rightarrow> bool" where
"garden_of_eden (CA s rule l r) = (\<not>(\<exists> s0. (CA s0 rule l r) yields s))"

fun reversible :: "CA \<Rightarrow> bool" where
"reversible (CA _ rule l r) = (\<forall>s. (\<exists>!s0. State (run_t_steps (CA s0 rule l r) 1) = s))"*)

fun mirror :: "rule \<Rightarrow> rule" where
"mirror r (Nb a b c)= r (Nb c b a)"

definition amphichiral :: "rule \<Rightarrow> bool" where
"amphichiral r \<equiv> r = (mirror r)"


subsection \<open>Concrete base examples\<close>

definition null_rule :: rule where
"null_rule _ = Zero"

fun r110 :: rule where
"r110  (Nb One One One) = Zero"   |
"r110  (Nb One One Zero) = One"   |
"r110  (Nb One Zero One) = One"   |
"r110  (Nb One Zero Zero) = Zero" |
"r110  (Nb Zero One One) = One"   |
"r110  (Nb Zero One Zero) = One"  |
"r110  (Nb Zero Zero One) = One"  |
"r110  (Nb Zero Zero Zero) = Zero"

end