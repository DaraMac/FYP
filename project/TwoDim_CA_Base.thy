theory TwoDim_CA_Base
  imports CA_Base
begin

datatype neighbourhood = Nb (NorthWest:cell) (North:cell) (NorthEast:cell)
                            (West:cell) (Centre:cell) (East:cell)
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

end