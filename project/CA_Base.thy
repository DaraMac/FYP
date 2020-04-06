chapter \<open>Cellular Automata Basics\<close>

theory CA_Base
  imports Main
begin

datatype cell = Zero | One

datatype neighbourhood = Nb cell cell cell
type_synonym rule = "neighbourhood \<Rightarrow> cell"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

fun flip :: "cell \<Rightarrow> cell" where
"flip One = Zero" |
"flip Zero = One"

fun flip_nb :: "neighbourhood \<Rightarrow> neighbourhood" where
"flip_nb (Nb a b c) = Nb (flip a) (flip b) (flip c)"

fun sum_nb :: "neighbourhood \<Rightarrow> nat" where
"sum_nb (Nb a b c) = count_list [a, b, c] One"


section \<open>Basic Rule Properties\<close>

fun mirror :: "rule \<Rightarrow> rule" where
"mirror r (Nb a b c)= r (Nb c b a)"

definition amphichiral :: "rule \<Rightarrow> bool" where
"amphichiral r \<equiv> r = (mirror r)"

fun complement :: "rule \<Rightarrow> rule" where
"complement r nb = flip (r (flip_nb nb))"

definition totalistic :: "rule \<Rightarrow> bool" where
"totalistic r \<equiv> (\<forall> nb1 nb2. sum_nb nb1 = sum_nb nb2 \<longrightarrow> (r nb1) = (r nb2))"


subsection \<open>Concrete rule examples\<close>

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