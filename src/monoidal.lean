import data.equiv.basic
import algebra.category.Mon.limits
import category_theory.monoidal.category
--import category_theory.limits.shapes.finite_products

open category_theory category_theory.limits category_theory.iso
open Mon

namespace category_theory.monoidal

def tensor_obj (M N : Mon) : Mon := Mon.of (↥M × ↥N)

def tensor_hom {M N M' N' : Mon} : (M ⟶ N) → (M' ⟶ N') → (tensor_obj M M' ⟶ tensor_obj N N') :=
λ f g, { to_fun := (λ p, (f p.1, g p.2)), map_one' := by tidy, map_mul' := by tidy }

def associator (X Y Z : Mon) : Mon.of (↥(Mon.of (↥X × ↥Y)) × ↥Z) ≅ Mon.of (↥X × ↥(Mon.of (↥Y × ↥Z))) :=
begin
  apply mul_equiv.to_Mon_iso,
  exact { to_fun := by rintro ⟨⟨x, y⟩, z⟩; exact (x, (y, z)),
  inv_fun := by rintro ⟨x, ⟨y, z⟩⟩; exact ((x, y), z),
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; refl,
  right_inv := by rintro ⟨x, ⟨y, z⟩⟩; refl,
  map_mul' := by rintros ⟨⟨x, y⟩,_⟩ ⟨⟨x, y⟩, _⟩; refl, }
end

def of_self_iso (M : Mon) : Mon.of M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

def product.lid (M : Mon) : of (punit × M) ≃* M :=
{to_fun := λ p, p.2,
 inv_fun := λ p, (1, p),
 left_inv := by intros x; cases x; cases x_fst; refl,
 right_inv := by intros x; refl,
 map_mul' := by intros x y; refl}

def product.rid (M : Mon) : of (M × punit) ≃* M :=
{to_fun := λ p, p.1,
 inv_fun := λ p, (p, 1),
 left_inv := by intros x; cases x; cases x_snd; refl,
 right_inv := by intros x; refl,
 map_mul' := by intros x y; refl}

def left_unitor (M : Mon) : Mon.of (↥(of punit) × ↥M) ≅ M :=
(mul_equiv.to_Mon_iso (product.lid M)).trans (of_self_iso M)

def right_unitor (M : Mon) : Mon.of (↥M × ↥(of punit)) ≅ M :=
(mul_equiv.to_Mon_iso (product.rid M)).trans (of_self_iso M)

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Mon}
  (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom (tensor_hom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
    (associator X₁ X₂ X₃).hom ≫ tensor_hom f₁ (tensor_hom f₂ f₃) := by ext; tidy

instance Mon_monoidal : monoidal_category Mon := {
  tensor_obj := tensor_obj,
  tensor_hom := @tensor_hom,
  tensor_unit := of punit,
  associator := associator,
  left_unitor := left_unitor,
  right_unitor := right_unitor,
  tensor_id' := begin intros, tidy, end,
  tensor_comp' := begin intros, tidy, end,
}

@[simp] lemma tensor_apply {W X Y Z : Mon} (f : W ⟶ X) (g : Y ⟶ Z) (p : tensor_obj W Y) :
(tensor_hom f g) p = (f p.1, g p.2) := rfl

@[simp] lemma left_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((λ_ X).hom : (𝟙_ (Mon)) ⊗ X → X) (p, x) = x := rfl
@[simp] lemma left_unitor_inv_apply {X : Mon} {x : X} :
  ((λ_ X).inv : X ⟶ (𝟙_ (Mon)) ⊗ X) x = (punit.star, x) := rfl

@[simp] lemma right_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((ρ_ X).hom : X ⊗ (𝟙_ (Mon)) → X) (x, p) = x := rfl
@[simp] lemma right_unitor_inv_apply {X : Mon} {x : X} :
  ((ρ_ X).inv : X ⟶ X ⊗ (𝟙_ (Mon))) x = (x, punit.star) := rfl

@[simp] lemma associator_hom_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)) ((x, y), z) = (x, (y, z)) := rfl
@[simp] lemma associator_inv_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).inv : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) := rfl

end category_theory.monoidal
