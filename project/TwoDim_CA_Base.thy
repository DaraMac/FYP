section \<open>2D Cellular Automata Base\<close>

theory TwoDim_CA_Base
  imports CA_Base
begin

datatype neighbourhood = Nb (NorthWest:cell) (North:cell) (NorthEast:cell)
                            (West:cell)      (Centre:cell)(East:cell)
                            (SouthWest:cell) (South:cell) (SouthEast:cell)

type_synonym rule = "neighbourhood \<Rightarrow> cell"

fun apply_nb :: "(cell \<Rightarrow> cell) \<Rightarrow> neighbourhood \<Rightarrow> neighbourhood" where
"apply_nb f (Nb nw n ne w c e sw s se) = Nb (f nw) (f n) (f ne) (f w) (f c) (f e) (f sw) (f s) (f se)"

fun nb_to_list :: "neighbourhood \<Rightarrow> cell list" where
"nb_to_list (Nb nw n ne w c e sw s se) = [nw, n, ne, w, c, e, sw, s, se]"

(* intentionally not total *)
fun list_to_nb :: "cell list \<Rightarrow> neighbourhood" where
"list_to_nb [nw, n, ne, w, c, e, sw, s, se] = Nb nw n ne w c e sw s se"


fun flip_nb :: "neighbourhood \<Rightarrow> neighbourhood" where
"flip_nb nb = apply_nb flip nb"

fun sum_nb :: "neighbourhood \<Rightarrow> nat" where
"sum_nb nb = count_list (nb_to_list nb) One"

definition outer_sum :: "neighbourhood \<Rightarrow> nat" where
"outer_sum nb = (case Centre nb of Zero \<Rightarrow> sum_nb nb |
                                   One \<Rightarrow> (sum_nb nb) - 1)"

lemma [simp] :"Centre nb = Zero \<Longrightarrow> outer_sum nb = sum_nb nb"
apply auto
using outer_sum_def by auto

fun complement :: "rule \<Rightarrow> rule" where
"complement r nb = flip (r (flip_nb nb))"

definition totalistic :: "rule \<Rightarrow> bool" where
"totalistic r \<equiv> (\<forall> nb1 nb2. sum_nb nb1 = sum_nb nb2 \<longrightarrow> (r nb1) = (r nb2))"

definition outer_totalistic :: "rule \<Rightarrow> bool" where
"outer_totalistic r \<equiv> (\<forall> nb1 nb2. (Centre nb1 = Centre nb2) \<longrightarrow> (outer_sum nb1 = outer_sum nb2) \<longrightarrow> (r nb1) = (r nb2))"

subsection \<open>Game of life \<close>

(* For One case we have 3 or 4 as we also count the cell in the middle *)
definition life :: rule where
"life nb = (case (Centre nb) of
            One   \<Rightarrow> (if (outer_sum nb) = 2 \<or> (outer_sum nb) = 3
                      then One else Zero) |
            Zero  \<Rightarrow> (if (outer_sum nb) = 3
                      then One else Zero))"

(* line balance *)
theorem "outer_totalistic life"
by apply(simp add: outer_totalistic_def life_def)

end
