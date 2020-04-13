section \<open>Elementary Cellular Automata Base\<close>

theory Elementary_CA_Base
  imports CA_Base
begin

datatype neighbourhood = Nb cell cell cell
type_synonym rule = "neighbourhood \<Rightarrow> cell"

fun apply_nb :: "(cell \<Rightarrow> cell) \<Rightarrow> neighbourhood \<Rightarrow> neighbourhood" where
"apply_nb f (Nb a b c) = Nb (f a) (f b) (f c)"

fun flip_nb :: "neighbourhood \<Rightarrow> neighbourhood" where
"flip_nb nb = apply_nb flip nb"

fun sum_nb :: "neighbourhood \<Rightarrow> nat" where
"sum_nb (Nb a b c) = count_list [a, b, c] One"


lemma flip_nb_cancel [simp]: "flip_nb (flip_nb nb) = nb"
apply(induction nb)
apply(auto)
done

lemma sum_nb_bound: "sum_nb nb \<le> 3"
apply(induction nb)
apply(auto)
done


subsection \<open>Basic Rule Properties\<close>

fun mirror :: "rule \<Rightarrow> rule" where
"mirror r (Nb a b c)= r (Nb c b a)"

lemma [simp]: "(mirror (mirror r)) a = r a"
apply(induction a)
apply(auto)
done


definition amphichiral :: "rule \<Rightarrow> bool" where
"amphichiral r \<equiv> (\<forall> c. r c = (mirror r) c)"

fun complement :: "rule \<Rightarrow> rule" where
"complement r nb = flip (r (flip_nb nb))"


lemma [simp]: "complement (complement r) a = r a"
apply(induction a)
apply auto
done


definition totalistic :: "rule \<Rightarrow> bool" where
"totalistic r \<equiv> (\<forall> nb1 nb2. sum_nb nb1 = sum_nb nb2 \<longrightarrow> (r nb1) = (r nb2))"


subsection \<open>Concrete rule examples\<close>

definition null_rule :: rule where
"null_rule _ = Zero"

fun r4 :: rule where
"r4  (Nb One  One  One)  = Zero" |
"r4  (Nb One  One  Zero) = Zero" |
"r4  (Nb One  Zero One)  = Zero" |
"r4  (Nb One  Zero Zero) = Zero" |
"r4  (Nb Zero One  One)  = Zero" |
"r4  (Nb Zero One  Zero) = One"  |
"r4  (Nb Zero Zero One)  = Zero" |
"r4  (Nb Zero Zero Zero) = Zero"


subsection \<open>Rule 110\<close>

fun r110 :: rule where
"r110  (Nb One  One  One)  = Zero" |
"r110  (Nb One  One  Zero) = One"  |
"r110  (Nb One  Zero One)  = One"  |
"r110  (Nb One  Zero Zero) = Zero" |
"r110  (Nb Zero One  One)  = One"  |
"r110  (Nb Zero One  Zero) = One"  |
"r110  (Nb Zero Zero One)  = One"  |
"r110  (Nb Zero Zero Zero) = Zero"

lemma "\<not>amphichiral r110"
by (metis amphichiral_def cell.distinct(1) mirror.simps r110.simps(4) r110.simps(7))

lemma "\<not>totalistic r110"
apply auto
apply(simp add: totalistic_def)
apply(rule allE)
apply auto
by (metis cell.simps(2) count_list.simps(2) r110.simps(4) r110.simps(6) sum_nb.simps)

end
