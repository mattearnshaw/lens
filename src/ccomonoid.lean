import category_theory.category.default
import category_theory.monoidal.category

universes u v

open category_theory

-- adapted from mjendrusch/monoidal-categories-reboot
class braided_monoidal_category (C : Type) [category C] extends monoidal_category C :=
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
(hexagon_forward'     : Π X Y Z : C,
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (associator Y X Z).hom ≫ (𝟙 Y ⊗ (braiding X Z).hom)
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (associator X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y))
  . obviously)

notation `σ` := braided_monoidal_category.braiding

class symmetric_monoidal_category (C : Type) [category.{v} C] 
extends braided_monoidal_category C : Type v :=
(symmetry' : ∀ X Y : C, (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y) . obviously)

variables {C : Type} [category C] [symmetric_monoidal_category C]

-- FIXME: should be able to infer [category C]
structure commutative_comonoid (C : Type) [category C] [symmetric_monoidal_category C] :=
(c : C) 
(ε : c ⟶ 𝟙_ C)
(δ : c ⟶ c ⊗ c)
(unit : δ ≫ ((𝟙 c) ⊗ ε) = (ρ_ c).inv) -- Spivak def 2.6#1
(commutative : δ ≫ (σ c c).hom = δ) -- Spivak def 2.6#2
(associative : δ ≫ ((𝟙 c) ⊗ δ) = δ ≫ (δ ⊗ (𝟙 c)) ≫ (α_ _ _ _).hom) -- Spivak def 2.6#3

/- morphism of commutative comonoids -/
structure hom_commutative_comonoid (c d : commutative_comonoid C) :=
(f : c.c ⟶ d.c)
(h₁ : c.ε = f ≫ d.ε)
(h₂ : c.δ ≫ (f ⊗ f) = f ≫ d.δ)

instance h : has_hom (commutative_comonoid C) := 
{ hom := hom_commutative_comonoid }

def comp (c d e : commutative_comonoid C) (f : c ⟶ d)  (g : d ⟶ e) : c ⟶ e :=
{ f := f.f ≫ g.f, 
  h₁ := begin
    rw f.h₁,
    rw g.h₁,
    rw eq_comm,
    exact category.assoc _ _ _,
  end, 
  h₂ :=  begin
    rw monoidal_category.tensor_comp,
    rw ← category.assoc,
    rw f.h₂,
    rw category.assoc,
    rw g.h₂,
    rw category.assoc,
  end }

instance h2 : category_struct (commutative_comonoid C) := 
{ comp := comp, id := λ _, ⟨𝟙 _, by rw category.id_comp, by obviously⟩,}

@[ext] lemma ext {c d : commutative_comonoid C} {f g : c ⟶ d} (h : f.f = g.f) : f = g := begin
  cases f,
  cases g,
  tidy,
end

lemma assoc' {W X Y Z : commutative_comonoid C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ g ≫ h := 
begin
  ext,
  have l₁ : (f ≫ g ≫ h).f = f.f ≫ g.f ≫ h.f, from rfl,
  rw l₁,
  have l₂ : ((f ≫ g) ≫ h).f = (f ≫ g).f ≫ h.f, from rfl,
  rw l₂,
  have l₃ : (f ≫ g).f = f.f ≫ g.f, from rfl,
  rw l₃,
  rw category.assoc',
end

instance cc_category : category (commutative_comonoid C) := 
{
  hom := λ c d, hom_commutative_comonoid c d,
  id := λ _, ⟨𝟙 _, by rw category.id_comp, by obviously⟩,
  comp := comp,
  comp_id' := λ c d f, by ext; exact category.comp_id' f.f,
  id_comp' := λ c d f, by ext; exact category.id_comp' f.f,
  assoc' := λ _ _ _ _ f g h, by exact assoc' f g h,
}