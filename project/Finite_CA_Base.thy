theory Finite_CA_Base
  imports CA_Base
begin

(* factor out Rule stuff even more and apply_t_times *)
section \<open>Base datatypes and definitions common to all Cellular Automata\<close>
(* Might end up having different bases between 1 and 2D*)
(* perhaps typeclass them so well-formed works on all? *)

subsection \<open>Basis type of all elementary 1D CA\<close>

type_synonym state = "cell list"

datatype CA = CA (State : state) (Rule : rule)

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

fun flip :: "cell \<Rightarrow> cell" where
"flip One = Zero" |
"flip Zero = One"

fun flip_nb :: "neighbourhood \<Rightarrow> neighbourhood" where
"flip_nb (Nb a b c) = Nb (flip a) (flip b) (flip c)"

fun sum_nb :: "neighbourhood \<Rightarrow> nat" where
"sum_nb (Nb a b c) = count_list [a, b, c] One"

fun mirror :: "rule \<Rightarrow> rule" where
"mirror r (Nb a b c)= r (Nb c b a)"

definition amphichiral :: "rule \<Rightarrow> bool" where
"amphichiral r \<equiv> r = (mirror r)"

fun complement :: "rule \<Rightarrow> rule" where
"complement r nb = flip (r (flip_nb nb))"

definition totalistic :: "rule \<Rightarrow> bool" where
"totalistic r \<equiv> (\<forall> nb1 nb2. sum_nb nb1 = sum_nb nb2 \<longrightarrow> (r nb1) = (r nb2))"


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