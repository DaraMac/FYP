theory TwoDim_CA_Base
  imports CA_Base
begin

datatype neighbourhood = Nb (NorthWest:cell) (North:cell) (NorthEast:cell)
                            (West:cell)      (Centre:cell)(East:cell)
                            (SouthWest:cell) (South:cell) (SouthEast:cell)

type_synonym rule = "neighbourhood \<Rightarrow> cell"

fun apply_nb :: "(cell \<Rightarrow> cell) \<Rightarrow> neighbourhood \<Rightarrow> neighbourhood" where
"apply_nb f (Nb nw n ne w c e sw s se) = Nb (f nw) (f n) (f ne) (f w) (f c) (f e) (f sw) (f s) (f se)"

fun list_nb :: "neighbourhood \<Rightarrow> cell list" where
"list_nb (Nb nw n ne w c e sw s se) = [nw, n, ne, w, c, e, sw, s, se]"

fun flip_nb :: "neighbourhood \<Rightarrow> neighbourhood" where
"flip_nb nb = apply_nb flip nb"

fun sum_nb :: "neighbourhood \<Rightarrow> nat" where
"sum_nb nb = count_list (list_nb nb) One"

fun complement :: "rule \<Rightarrow> rule" where
"complement r nb = flip (r (flip_nb nb))"

definition totalistic :: "rule \<Rightarrow> bool" where
"totalistic r \<equiv> (\<forall> nb1 nb2. sum_nb nb1 = sum_nb nb2 \<longrightarrow> (r nb1) = (r nb2))"


subsection \<open>Game of life \<close>

(* For One case we have 3 or 4 as we also count the cell in the middle *)
definition life :: rule where
"life ca = (case (Centre ca) of
            One   \<Rightarrow> (if (sum_nb ca) = 3 \<or> (sum_nb ca) = 4
                      then One else Zero) |
            Zero  \<Rightarrow> (if (sum_nb ca) = 3
                      then One else Zero))"
end