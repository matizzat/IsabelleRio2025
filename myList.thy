theory myList
  imports Main
begin

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ly = ly" |
"app (Cons x lx) ly = Cons x (app lx ly)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" | 
"rev (Cons x lx) = app (rev lx) (Cons x Nil)"

theorem app_associative: "app (app x y) z = app x (app y z)"
  apply(induction x)
   apply auto
  done 

lemma app_nil_right: "app x Nil = x"
  apply(induction x)
   apply auto
  done

lemma rev_app: "rev (app x y) = app (rev y) (rev x)"
  apply(induction x)
  subgoal
    apply auto
    apply(subst app_nil_right)
    apply(rule refl)
    done 
  subgoal
    apply auto
    apply(subst app_associative)
    apply(rule refl)
    done
  done

lemma rev_rev: "rev (rev x) = x"
  apply(induction x)
   apply(auto)
  apply(subst rev_app)
  apply(auto)
  done

end