theory ATM
  imports Main

begin

type_synonym plane = "int \<times> int"

fun North :: "plane \<Rightarrow> plane" where
"North (x, y) = (x, y+1)"

fun East :: "plane \<Rightarrow> plane" where
"East (x, y) = (x+1, y)"

fun South :: "plane \<Rightarrow> plane" where
"South (x, y) = (x, y-1)"

fun West :: "plane \<Rightarrow> plane" where
"West (x, y) = (x-1, y)"

(*type_synonym direction = "plane \<Rightarrow> plane"*)
datatype direction = N | E | S | W

(* inverse of directions *)
(* maybe prove basic properties? *)
fun inv_d :: "direction \<Rightarrow> direction" where
"inv_d N = S" |
"inv_d S = N" |
"inv_d E = W" |
"inv_d W = E"

(*
definition D :: "(plane \<Rightarrow> plane) set" where
"D = {N, E, S, W}"

fun neighbours :: "plane \<Rightarrow> plane \<Rightarrow> bool" where
"neighbours p q = (if q \<in> {N p, E p, S p, W p} then True else False)"


lemma east_inverse [simp]: "E (W p) = p"
  apply (induction p)
  apply auto
  done*)



(* binding domain *)
datatype bind_dom = bind string nat | null 

(* N E S W *)
datatype tile = tile bind_dom bind_dom bind_dom bind_dom

definition empty_tile :: tile where
"empty_tile = tile null null null null"

(* I want to enforce directions coming from a type D,
while still being functions *)
fun bd :: "direction \<Rightarrow> tile \<Rightarrow> bind_dom" where
"bd N (tile n _ _ _) = n" |
"bd E (tile _ e _ _) = e" |
"bd S (tile _ _ s _) = s" |
"bd W (tile _ _ _ w) = w"

(*fun is_strength_function :: "(bind_dom \<Rightarrow> bind_dom \<Rightarrow> nat) \<Rightarrow> bool" where*)
type_synonym strength_function = "bind_dom \<Rightarrow> bind_dom \<Rightarrow> nat"

(* doesn't enforce equality of n and k strengths!*)
fun g :: strength_function  where
"g (bind a n) (bind b k) = (if a = b then n else 0)" |
"g null _ = 0" |
"g _ null = 0"

type_synonym configuration = "plane \<Rightarrow> tile"

definition unit_tile :: tile where
"unit_tile = tile (bind ''a'' 1) (bind ''a'' 1) (bind ''a'' 1) (bind ''a'' 1)"


fun test_conf :: configuration where
"test_conf p = (if p = (0,0) \<or> p = (0,1) then unit_tile else empty_tile)"

value "test_conf (1, 0)"


type_synonym binding = "configuration
                        \<Rightarrow> direction
                        \<Rightarrow> plane
                        \<Rightarrow> nat"



(* didn't like A being defined outside *)
(* define inverse directions *)
fun g_bind :: binding where
"g_bind A D p = (case D of 
                N \<Rightarrow> g (bd D (A p)) (bd (inv_d D) (A (North p))) |
                E \<Rightarrow> g (bd D (A p)) (bd (inv_d D) (A (East p)))  |
                W \<Rightarrow> g (bd D (A p)) (bd (inv_d D) (A (West p)))  |
                S \<Rightarrow> g (bd D (A p)) (bd (inv_d D) (A (South p))))"

value "test_conf (0,0)"
value "g_bind test_conf N (0,0)"

fun t_conf :: "tile \<Rightarrow>plane  \<Rightarrow> configuration" where
"t_conf t p k = (if p = k then t else empty_tile)"

fun empty_conf :: configuration where
"empty_conf k = t_conf empty_tile (0,0) k"

type_synonym tile_set = "tile set"

(* I'd like to define as a configuration *)
type_synonym seed = tile

type_synonym temp = nat

(* I want to enforce finiteness of T on a type level *)
type_synonym tile_system = "tile_set\<times>seed\<times>temp"

fun update_system :: "tile_system \<Rightarrow> configuration \<Rightarrow>configuration" where
"update_system (T, S, t) A B = 






end