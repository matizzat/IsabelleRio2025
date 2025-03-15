theory myNatural
  imports Main
begin

(* Deactivate a few standard concepts *)

datatype Nat' = Z | S Nat'

fun add :: "Nat' \<Rightarrow> Nat' \<Rightarrow> Nat'" where
"add Z n = n" |
"add (S m) n = S (add m n)"

lemma add_Z_right[simp]: "add n Z = n"
  apply(induction n)
  apply auto
  done

lemma add_associative: "add (add a b) c = add a (add b c)"
  apply (induction a)
   apply(auto)
  done

lemma add_suc_swap: "add (S a) b = add a (S b)"
  apply (induction a)
   apply auto
  done

lemma add_conmutative: "add a b = add b a"
  apply (induction a)
   apply auto
  apply (subst add.simps(2)[symmetric])
  apply (subst add_suc_swap)
  apply auto
  done

fun double :: "Nat' \<Rightarrow> Nat'" where
"double Z = Z" | 
"double (S n) = S (S (double n))" 

lemma "double n = add n n"
  apply(induction n)
   apply auto
  apply(subst add.simps(2)[symmetric])
  apply(subst add_suc_swap)
  apply auto
  done

end