import algebra.category.Mon.monoidal
import category_theory.monoidal.internal
import category_theory.limits.shapes.types

open category_theory
open category_theory.monoidal
open category_theory.limits

namespace Mon_Mon_equivalence_CommMon

def monoidal_Mon : monoidal_category Mon := category_theory.monoidal.Mon_monoidal

def functor : (@Mon_ Mon _ monoidal_Mon) ⥤ CommMon :=
{ obj := λ A, ⟨ A.X,
  { one := A.one 1,
    mul := λ x y, A.mul (x, y),
    one_mul := begin intro,
      have := congr_fun A.one_mul _,
      end,
    mul_one := sorry,
    mul_assoc := sorry,
    mul_comm := sorry, }⟩,
  map := λ A B f,
  { to_fun := f.hom,
    map_one' := sorry, -- type mismatch at field 'map_one'' ... f.hom has type @eq (@coe_sort
    map_mul' := sorry, }, }

/-
def inverse : Mon.{u} ⥤ Mon_ (Type u) :=
{ obj := λ A,
  { X := A,
    one := λ _, 1,
    mul := λ p, p.1 * p.2,
    mul_assoc' := by { ext ⟨⟨x, y⟩, z⟩, simp [mul_assoc], }, },
  map := λ A B f,
  { hom := f, }, }.
-/

/-
def Mon_Mon_equivalence_CommMon : Mon_ Mon ≌ CommMon :=
{ functor := functor,
  inverse := inverse,
  unit_iso := nat_iso.of_components
    (λ A, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, }})
    (by tidy),
  counit_iso := nat_iso.of_components (λ A,
  { hom := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, },
    inv := { to_fun := id, map_one' := rfl, map_mul' := λ x y, rfl, }}) (by tidy), }.

-/

end Mon_Mon_equivalence_CommMon
