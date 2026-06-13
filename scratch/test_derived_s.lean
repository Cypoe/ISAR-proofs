import ISAR

namespace ISAR

/-- Custom syntactic rewrite relation including dup and swap rules. -/
inductive IStep' : ITerm → ITerm → Prop where
  | normβ (x : ITerm) :
      IStep' (ITerm.app ITerm.norm x) x
  | konstβ (x y : ITerm) :
      IStep' (ITerm.app (ITerm.app ITerm.konst x) y) x
  | compβ (f g x : ITerm) :
      IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.comp f) g) x)
             (ITerm.app f (ITerm.app g x))
  | dupβ (f x : ITerm) :
      IStep' (ITerm.app (ITerm.app ITerm.dup f) x)
             (ITerm.app (ITerm.app f x) x)
  | swapβ (f x y : ITerm) :
      IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.swap f) x) y)
             (ITerm.app (ITerm.app f y) x)
  | appL {f f' x : ITerm} :
      IStep' f f' → IStep' (ITerm.app f x) (ITerm.app f' x)
  | appR {f x x' : ITerm} :
      IStep' x x' → IStep' (ITerm.app f x) (ITerm.app f x')

abbrev IRed' := Relation.ReflTransGen IStep'

def s_isar : ITerm :=
  ITerm.app (ITerm.app ITerm.comp (ITerm.app ITerm.comp ITerm.dup))
    (ITerm.app (ITerm.app ITerm.swap
      (ITerm.app (ITerm.app ITerm.comp ITerm.comp)
        (ITerm.app (ITerm.app ITerm.comp ITerm.comp) ITerm.swap)))
      ITerm.norm)

/-- Auxiliary step lemmas to make the proof extremely clean. -/
theorem step_appL {f f' x : ITerm} (h : IStep' f f') : IStep' (ITerm.app f x) (ITerm.app f' x) :=
  IStep'.appL h

theorem step_appR {f x x' : ITerm} (h : IStep' x x') : IStep' (ITerm.app f x) (ITerm.app f x') :=
  IStep'.appR h

theorem red_appL {f f' x : ITerm} (h : IRed' f f') : IRed' (ITerm.app f x) (ITerm.app f' x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (step_appL hstep)

theorem red_appR {f x x' : ITerm} (h : IRed' x x') : IRed' (ITerm.app f x) (ITerm.app f x') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (step_appR hstep)

theorem red_trans {t u v : ITerm} (h1 : IRed' t u) (h2 : IRed' u v) : IRed' t v :=
  Relation.ReflTransGen.trans h1 h2

/--
Theorem: Derived S behavior.
Using the IRAS operator basis, the composite term s_isar reduces
to the standard S-combinator behavior.
-/
theorem s_isar_beta (x y z : ITerm) :
    IRed' (ITerm.app (ITerm.app (ITerm.app s_isar x) y) z)
          (ITerm.app (ITerm.app x z) (ITerm.app y z)) := by
  let P := ITerm.app (ITerm.app ITerm.swap
            (ITerm.app (ITerm.app ITerm.comp ITerm.comp)
              (ITerm.app (ITerm.app ITerm.comp ITerm.comp) ITerm.swap)))
            ITerm.norm
  -- 1. Outer comp reduction
  have h1 : IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app ITerm.comp ITerm.dup)) P) x)
                   (ITerm.app (ITerm.app ITerm.comp ITerm.dup) (ITerm.app P x)) :=
    IStep'.compβ (ITerm.app ITerm.comp ITerm.dup) P x
  have h2 : IRed' (ITerm.app (ITerm.app (ITerm.app s_isar x) y) z)
                  (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp ITerm.dup) (ITerm.app P x)) y) z) :=
    red_appL (red_appL (Relation.ReflTransGen.single h1))

  -- 2. Second comp reduction
  have h3 : IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.comp ITerm.dup) (ITerm.app P x)) y)
                   (ITerm.app ITerm.dup (ITerm.app (ITerm.app P x) y)) :=
    IStep'.compβ ITerm.dup (ITerm.app P x) y
  have h4 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp ITerm.dup) (ITerm.app P x)) y) z)
                  (ITerm.app (ITerm.app ITerm.dup (ITerm.app (ITerm.app P x) y)) z) :=
    red_appL (Relation.ReflTransGen.single h3)

  -- 3. Dup reduction
  have h5 : IStep' (ITerm.app (ITerm.app ITerm.dup (ITerm.app (ITerm.app P x) y)) z)
                   (ITerm.app (ITerm.app (ITerm.app (ITerm.app P x) y) z) z) :=
    IStep'.dupβ (ITerm.app (ITerm.app P x) y) z
  have h6 : IRed' (ITerm.app (ITerm.app (ITerm.app s_isar x) y) z)
                  (ITerm.app (ITerm.app (ITerm.app (ITerm.app P x) y) z) z) :=
    red_trans h2 (red_trans h4 (Relation.ReflTransGen.single h5))

  -- 4. Swap reduction on P x
  let Q := ITerm.app (ITerm.app ITerm.comp ITerm.comp)
            (ITerm.app (ITerm.app ITerm.comp ITerm.comp) ITerm.swap)
  have h7 : IStep' (ITerm.app P x) (ITerm.app (ITerm.app Q x) ITerm.norm) :=
    IStep'.swapβ Q ITerm.norm x
  have h8 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app P x) y) z) z)
                  (ITerm.app (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q x) ITerm.norm) y) z) z) :=
    red_appL (red_appL (red_appL (Relation.ReflTransGen.single h7)))

  -- 5. Reduce Q x
  let Q2 := ITerm.app (ITerm.app ITerm.comp ITerm.comp) ITerm.swap
  have h9 : IStep' (ITerm.app Q x) (ITerm.app ITerm.comp (ITerm.app Q2 x)) :=
    IStep'.compβ ITerm.comp Q2 x
  have h10 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q x) ITerm.norm) y) z) z)
                   (ITerm.app (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app Q2 x)) ITerm.norm) y) z) z) :=
    red_appL (red_appL (red_appL (red_appL (Relation.ReflTransGen.single h9))))

  -- 6. Comp reduction on Q2 x and norm
  have h11 : IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app Q2 x)) ITerm.norm) y)
                    (ITerm.app (ITerm.app Q2 x) (ITerm.app ITerm.norm y)) :=
    IStep'.compβ (ITerm.app Q2 x) ITerm.norm y
  have h12 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app Q2 x)) ITerm.norm) y) z) z)
                   (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q2 x) (ITerm.app ITerm.norm y)) z) z) :=
    red_appL (red_appL (Relation.ReflTransGen.single h11))

  -- 7. Norm reduction
  have h13 : IStep' (ITerm.app ITerm.norm y) y :=
    IStep'.normβ y
  have h14 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q2 x) (ITerm.app ITerm.norm y)) z) z)
                   (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q2 x) y) z) z) :=
    red_appL (red_appL (red_appR (Relation.ReflTransGen.single h13)))

  -- 8. Reduce Q2 x
  have h15 : IStep' (ITerm.app Q2 x) (ITerm.app ITerm.comp (ITerm.app ITerm.swap x)) :=
    IStep'.compβ ITerm.comp ITerm.swap x
  have h16 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app Q2 x) y) z) z)
                   (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app ITerm.swap x)) y) z) z) :=
    red_appL (red_appL (red_appL (Relation.ReflTransGen.single h15)))

  -- 9. Comp reduction on swap x
  have h17 : IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app ITerm.swap x)) y) z)
                    (ITerm.app (ITerm.app ITerm.swap x) (ITerm.app y z)) :=
    IStep'.compβ (ITerm.app ITerm.swap x) y z
  have h18 : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app ITerm.comp (ITerm.app ITerm.swap x)) y) z) z)
                   (ITerm.app (ITerm.app (ITerm.app ITerm.swap x) (ITerm.app y z)) z) :=
    red_appL (Relation.ReflTransGen.single h17)

  -- 10. Swap reduction on x and y z
  have h19 : IStep' (ITerm.app (ITerm.app (ITerm.app ITerm.swap x) (ITerm.app y z)) z)
                    (ITerm.app (ITerm.app x z) (ITerm.app y z)) :=
    IStep'.swapβ x (ITerm.app y z) z

  -- Chain all reductions together
  have h_chain : IRed' (ITerm.app (ITerm.app (ITerm.app (ITerm.app P x) y) z) z)
                       (ITerm.app (ITerm.app x z) (ITerm.app y z)) :=
    red_trans h8 (red_trans h10 (red_trans h12 (red_trans h14 (red_trans h16 (red_trans h18 (Relation.ReflTransGen.single h19))))))

  exact red_trans h6 h_chain


end ISAR
