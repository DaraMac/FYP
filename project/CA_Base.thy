theory CA_Base
  imports Main
begin

datatype cell = Zero | One

fun flip :: "cell \<Rightarrow> cell" where
"flip One = Zero" |
"flip Zero = One"

fun apply_t_times :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
"apply_t_times f a 0 = a" |
"apply_t_times f a (Suc n) = apply_t_times f (f a) n"

end