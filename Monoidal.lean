import Mathlib.CategoryTheory.Products.Bifunctor

open CategoryTheory

namespace Quantum

universe v v₁ v₂ v₃ v₄ v₅ v₆ u u₁ u₂ u₃ u₄ u₅ u₆

variable (𝒞 : Type u₁) [Category.{v₁} 𝒞]

class MonoidalCategoryData where
  tensorProduct : 𝒞 × 𝒞 ⥤ 𝒞
  unitObject : 𝒞
  associator (A B C : 𝒞) : tensorProduct.obj ((tensorProduct.obj (A, B)), C) ≅ tensorProduct.obj (A, (tensorProduct.obj (B, C)))
  leftUnitor (A : 𝒞) : tensorProduct.obj (unitObject, A) ≅ A
  rightUnitor (A : 𝒞) : tensorProduct.obj (A, unitObject) ≅ A

scoped notation:70 lhs:71 "⊗" rhs:70 => MonoidalCategoryData.tensorProduct.obj (lhs, rhs)
scoped notation:70 lhs:71 "⊕" rhs:70 => MonoidalCategoryData.tensorProduct.map (lhs, rhs)
scoped notation "𝕀" => MonoidalCategoryData.unitObject
scoped notation "α" => MonoidalCategoryData.associator
scoped notation "γ" => MonoidalCategoryData.leftUnitor
scoped notation "ρ" => MonoidalCategoryData.rightUnitor

class MonoidalCategory extends MonoidalCategoryData 𝒞 where
  triangle (A B : 𝒞) : (α A 𝕀 B).hom ≫ ((𝟙 A) ⊕ (γ B).hom) = ((ρ A).hom ⊕ (𝟙 B) : (A ⊗ 𝕀) ⊗ B ⟶ A ⊗ B)
  pentagon (A B C D : 𝒞) : ((α A B C).hom ⊕ (𝟙 D)) ≫ (α A (B ⊗ C) D).hom ≫ ((𝟙 A) ⊕ (α B C D).hom) = (α (A ⊗ B) C D).hom ≫ (α A B (C ⊗ D)).hom

variable (ℳ : Type u₂) [Category.{v₂} ℳ] [MonoidalCategory ℳ]

@[simp] theorem interchange_law {A B C D E F : ℳ} (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ E) (j : E ⟶ F) : ((f ≫ g) ⊕ (h ≫ j)) = (f ⊕ h : (A ⊗ D) ⟶ (B ⊗ E)) ≫ (g ⊕ j : (B ⊗ E) ⟶ (C ⊗ F)) := by
  have fh1 : f = (f, h).1 := by simp
  have fh2 : h = (f, h).2 := by simp
  have gj1 : g = (g, j).1 := by simp
  have gj2 : j = (g, j).2 := by simp
  rw [fh1, fh2, gj1, gj2, ←prod_comp, Functor.map_comp]

def State (A : ℳ) := 𝕀 ⟶ A

class WellPointedMonoidalCategory extends MonoidalCategory ℳ where
  wellPointed : ∀ A B : ℳ, ∀ f g : A ⟶ B, ∀ a : State ℳ A, a ≫ f = a ≫ g → f = g

/- This definition is just for n = 2. Andrej Bauer says that the case for general n follows from just the cases for n = 0 and n = 2. TODO: Figure out what he means by this and implement it properly. -/
class MonoidallyWellPointedMonoidalCategory extends MonoidalCategory ℳ where
  monoidallyWellPointed : ∀ A₁ A₂ B : ℳ, ∀ f g : (A₁ ⊗ A₂) ⟶ B,∀ a₁ : State ℳ A₁, ∀ a₂ : State ℳ A₂, (a₁ ⊕ a₂) ≫ f = ((a₁ ⊕ a₂) : (𝕀 ⊗ 𝕀) ⟶ (A₁ ⊗ A₂)) ≫ g → f = g

def JointState (A : ℳ) (B : ℳ) := State ℳ (A ⊗ B)

def ProductState (c : JointState ℳ A B) := ∃ a : State ℳ A, ∃ b : State ℳ B, c = inv (γ 𝕀).hom ≫ ((a ⊕ b) : (𝕀 ⊗ 𝕀) ⟶ (A ⊗ B))

def EntangledState (c : JointState ℳ A B) := ¬ ProductState ℳ c

def Effect (A : ℳ) := A ⟶ 𝕀

class BraidedMonoidalCategoryData extends MonoidalCategory ℳ where
  braiding : ∀ A B : ℳ, (A ⊗ B) ≅ (B ⊗ A)

scoped notation "σ" => BraidedMonoidalCategoryData.braiding

class BraidedMonoidalCategory extends BraidedMonoidalCategoryData ℳ where
  hexagon1 : ∀ A B C : ℳ, (σ A (B ⊗ C)).hom = (α A B C).inv ≫ ((σ A B).hom ⊕ (𝟙 C) : (A ⊗ B) ⊗ C ⟶ (B ⊗ A) ⊗ C) ≫ (α B A C).hom ≫ ((𝟙 B) ⊕ (σ A C).hom) ≫ (α B C A).inv
  hexagon2 : ∀ A B C : ℳ, (σ (A ⊗ B) C).hom = (α A B C).hom ≫ ((𝟙 A) ⊕ (σ B C).hom : A ⊗ (B ⊗ C) ⟶ A ⊗ (C ⊗ B)) ≫ (α A C B).inv ≫ ((σ A C).hom ⊕ (𝟙 B)) ≫ (α C A B).hom

variable (ℬ: Type u₃) [Category.{v₃} ℬ] [BraidedMonoidalCategory ℬ]

class SymmetricMonoidalCategory extends BraidedMonoidalCategory ℬ where
  symmetry : ∀ A B : ℬ, (σ A B).hom ≫ (σ B A).hom = 𝟙 (A ⊗ B)

variable (𝒮 : Type u₄) [Category.{v₄} 𝒮] [SymmetricMonoidalCategory 𝒮]

@[simp] lemma symmetry_inv (A B : 𝒮) : (σ A B).hom = (σ B A).inv := by
  have : (σ B A).hom ≫ (σ B A).inv = (𝟙 (B ⊗ A)) := by simp
  rw [←SymmetricMonoidalCategory.symmetry] at this
  aesop_cat

class StrictMonoidalCategory extends MonoidalCategory ℳ where
  associatorStrictness : ∀ A B C : ℳ, (A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)
  leftUnitorStrictness : ∀ A : ℳ, 𝕀 ⊗ A = A
  rightUnitorStrictness : ∀ A : ℳ, A ⊗ 𝕀 = A

variable (𝒯 : Type u₅) [Category.{v₅} 𝒯] [StrictMonoidalCategory 𝒯]

variable (ℳ₁ : Type u) [Category.{v} ℳ₁] [MonoidalCategory ℳ₁]

variable (ℬ₁ : Type u) [Category.{v} ℬ₁] [BraidedMonoidalCategory ℬ₁]

variable (𝒮₁ : Type u) [Category.{v} 𝒮₁] [SymmetricMonoidalCategory 𝒮₁]

structure MonoidalFunctor extends Functor ℳ ℳ₁ where
  F₂ : ∀ A B : ℳ, (obj A) ⊗ (obj B) ≅ obj (A ⊗ B)
  F₀ : (𝕀 : ℳ₁) ≅ obj (𝕀 : ℳ)
  associatorPreserving : ∀ A B C : ℳ, (α (obj A) (obj B) (obj C)).hom ≫ (𝟙 (obj A) ⊕ (F₂ B C).hom) ≫ (F₂ A (B ⊗ C)).hom = ((F₂ A B).hom ⊕ 𝟙 (obj C)) ≫ (F₂ (A ⊗ B) C).hom ≫ map (α A B C).hom
  leftUnitorPreserving : ∀ A : ℳ, (γ (obj A)).hom ≫ map (γ A).inv = (F₀.hom ⊕ 𝟙 (obj A)) ≫ (F₂ 𝕀 A).hom
  rightUnitorPrserving : ∀ A : ℳ, (ρ (obj A)).hom ≫ map (ρ A).inv = (𝟙 (obj A) ⊕ F₀.hom) ≫ (F₂ A 𝕀).hom

structure BraidedMonoidalFunctor extends MonoidalFunctor ℬ ℬ₁ where
  braidingPreserving : ∀ A B : ℬ, (σ (obj A) (obj B)).hom ≫ (F₂ B A).hom = (F₂ A B).hom ≫ map (σ A B).hom

def SymmetricMonoidalFunctor := BraidedMonoidalFunctor 𝒮 𝒮₁

def MonoidallyEquivalent (F : MonoidalFunctor ℳ ℳ₁) := Functor.IsEquivalence F.toFunctor

structure MonoidalNatTrans (F G : MonoidalFunctor ℳ ℳ₁) extends NatTrans F.toFunctor G.toFunctor where
  F₂Naturality : ∀ A B : ℳ, (F.F₂ A B).hom ≫ app (A ⊗ B) = (app A ⊕ app B) ≫ (G.F₂ A B).hom
  F₀Naturality : F.F₀.hom ≫ app 𝕀 = G.F₀.hom

def BraidedMonoidalNatTrans := MonoidalNatTrans ℬ ℬ₁

def SymmetricMonoidalNatTrans := MonoidalNatTrans 𝒮 𝒮₁

/- The data for the strict monoidal category defined for the strictification theorem. -/

@[ext] structure StrictificationCatObj where
  F : ℳ ⥤ ℳ
  η (A B : ℳ) : (F.obj A) ⊗ B ≅ F.obj (A ⊗ B)

@[ext] structure StrictificationCatHom (F F' : StrictificationCatObj ℳ) where
  θ : NatTrans F.F F'.F
  condition (A B : ℳ) : (F.η A B).hom ≫ θ.app (A ⊗ B) = ((θ.app A) ⊕ (𝟙 B)) ≫ (F'.η A B).hom

def StrictificationCatId (F : StrictificationCatObj ℳ) : StrictificationCatHom ℳ F F where
  θ := NatTrans.id F.F
  condition A B := by rw [NatTrans.id_app', Category.comp_id, NatTrans.id_app', Bifunctor.map_id, Category.id_comp]

def StrictificationCatComp (F : StrictificationCatHom ℳ X Y) (F' : StrictificationCatHom ℳ Y Z) : StrictificationCatHom ℳ X Z where
  θ := NatTrans.vcomp F.θ F'.θ
  condition A B := by rw [NatTrans.vcomp_eq_comp, NatTrans.comp_app, NatTrans.comp_app, ←Category.comp_id (𝟙 B), interchange_law, ←Category.assoc, F.condition]; nth_rewrite 2 [Category.assoc]; rw [←F'.condition, Category.assoc]

theorem StrictificationCatIdComp (F : StrictificationCatHom ℳ X Y) : StrictificationCatComp ℳ (StrictificationCatId ℳ X) F = F := by 
  rw [StrictificationCatComp, StrictificationCatId]
  have : (NatTrans.id X.F).vcomp F.θ = F.θ := by rw [NatTrans.vcomp_eq_comp]; ext x; rw [NatTrans.comp_app, NatTrans.id_app', Category.id_comp]
  simp_rw [this]

theorem StrictificationCatCompId (F : StrictificationCatHom ℳ X Y) : StrictificationCatComp ℳ F (StrictificationCatId ℳ Y) = F := by
  rw [StrictificationCatComp, StrictificationCatId]
  have : F.θ.vcomp (NatTrans.id Y.F) = F.θ := by rw [NatTrans.vcomp_eq_comp]; ext x; rw [NatTrans.comp_app, NatTrans.id_app', Category.comp_id]
  simp_rw [this]

theorem StrictificationCatAssoc (F : StrictificationCatHom ℳ W X) (G : StrictificationCatHom ℳ X Y) (H : StrictificationCatHom ℳ Y Z) : StrictificationCatComp ℳ (StrictificationCatComp ℳ F G) H = StrictificationCatComp ℳ F (StrictificationCatComp ℳ G H) := by
  repeat rw [StrictificationCatComp]
  simp

instance StrictificationCat : Category (StrictificationCatObj ℳ) where
  Hom X Y := StrictificationCatHom ℳ X Y
  id X := StrictificationCatId ℳ X
  comp X Y := StrictificationCatComp ℳ X Y
  id_comp F := StrictificationCatIdComp ℳ F
  comp_id F := StrictificationCatCompId ℳ F
  assoc F G H := StrictificationCatAssoc ℳ F G H

/- Tensor product data -/

def StrictificationTensorProductObjEta (F F' : StrictificationCatObj ℳ): Iso ((F.F.obj (F'.F.obj A)) ⊗ B) (F.F.obj (F'.F.obj (A ⊗ B))) where
  hom := (F.η (F'.F.obj A) B).hom ≫ F.F.map (F'.η A B).hom
  inv := F.F.map (F'.η A B).inv ≫ (F.η (F'.F.obj A) B).inv

def StrictificationTensorProductObj (F F' : StrictificationCatObj ℳ) : StrictificationCatObj ℳ where
  F := F'.F ⋙ F.F
  η (_ _ : ℳ) := StrictificationTensorProductObjEta ℳ F F'

@[simp] lemma tensor_product_functor : (StrictificationTensorProductObj ℳ F F').F = F'.F ⋙ F.F := rfl

@[simp] lemma tensor_product_eta : ((StrictificationTensorProductObj ℳ F F').η A B).hom = (F.η (F'.F.obj A) B).hom ≫ F.F.map (F'.η A B).hom:= rfl

def StrictificationTensorProductMapTheta (θ : F ⟶ F') (θ' : G ⟶ G') : NatTrans (StrictificationTensorProductObj ℳ F G).F (StrictificationTensorProductObj ℳ F' G').F where
  app A := θ.θ.app (G.F.obj A) ≫ F'.F.map (θ'.θ.app A)
  naturality A B f := by 
    simp
    have : F'.F.map (G.F.map f) ≫ F'.F.map (θ'.θ.app B) = F'.F.map (θ'.θ.app A) ≫ F'.F.map (G'.F.map f) := by rw [←Functor.map_comp, ←Functor.map_comp, NatTrans.naturality]
    rw [this]

def StrictificationTensorProductMap (θ : F ⟶ F') (θ' : G ⟶ G') : (StrictificationTensorProductObj ℳ F G) ⟶ (StrictificationTensorProductObj ℳ F' G') where
  θ := StrictificationTensorProductMapTheta ℳ θ θ'
  condition A B := by
    rw [StrictificationTensorProductMapTheta]
    simp
    rw [←Category.comp_id (𝟙 B), interchange_law]; 
    have tri1 : (F.η (G.F.obj A) B).hom ≫ (F.η (G.F.obj A) B).inv ≫ ((θ.θ.app (G.F.obj A)) ⊕ (𝟙 B)) = ((θ.θ.app (G.F.obj A)) ⊕ (𝟙 B) : F.F.obj (G.F.obj A) ⊗ B ⟶ F'.F.obj (G.F.obj A) ⊗ B) := Iso.hom_inv_id_assoc (F.η (G.F.obj A) B)  ((θ.θ.app (G.F.obj A)) ⊕ (𝟙 B) : F.F.obj (G.F.obj A) ⊗ B ⟶ F'.F.obj (G.F.obj A) ⊗ B)
    have tri2 : F'.F.map (θ'.θ.app (A ⊗ B)) = F'.F.map (θ'.θ.app (A ⊗ B)) ≫ F'.F.map (G'.η A B).inv ≫ F'.F.map (G'.η A B).hom := by rw [Iso.map_inv_hom_id, Category.comp_id]
    have sq1 : (θ.θ.app (G.F.obj A ⊗ B)) ≫ (F'.η (G.F.obj A) B).inv ≫ ((F'.F.map (θ'.θ.app A)) ⊕ (𝟙 B)) = (F.η (G.F.obj A) B).inv ≫ ((θ.θ.app (G.F.obj A)) ⊕ (𝟙 B)) ≫ ((F'.F.map (θ'.θ.app A)) ⊕ (𝟙 B) : F'.F.obj (G.F.obj A) ⊗ B ⟶ F'.F.obj (G'.F.obj A) ⊗ B) := by 
      have := whisker_eq (F.η (G.F.obj A) B).inv (θ.condition (G.F.obj A) B)
      rw [Iso.inv_hom_id_assoc] at this
      rw [this, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]
    sorry

lemma tensor_product_obj_id : StrictificationCatHom.θ (𝟙 (StrictificationTensorProductObj ℳ F F')) = NatTrans.id (StrictificationTensorProductObj ℳ F F').F := rfl

lemma cat_obj_id_app {F : StrictificationCatObj ℳ} : (StrictificationCatHom.θ (𝟙 F)).app A = (NatTrans.id F.F).app A := rfl

lemma tensor_product_map_comp {A :  StrictificationTensorProductObj ℳ F G ⟶ StrictificationTensorProductObj ℳ F' G'} {B : StrictificationTensorProductObj ℳ F' G' ⟶ StrictificationTensorProductObj ℳ F'' G''} : (A ≫ B).θ.app X = (NatTrans.vcomp A.θ B.θ).app X := rfl

lemma cat_hom_comp_app {A B C : StrictificationCatObj ℳ} {F : A ⟶ B} {F' : B ⟶ C} : (F ≫ F').θ.app X = (F.θ.vcomp F'.θ).app X := rfl

def StrictificationTensorProduct : ((StrictificationCatObj ℳ) × (StrictificationCatObj ℳ)) ⥤ (StrictificationCatObj ℳ) where
  obj C := StrictificationTensorProductObj ℳ C.1 C.2
  map F := StrictificationTensorProductMap ℳ F.1 F.2
  map_id X := by
    apply StrictificationCatHom.ext
    simp
    rw [tensor_product_obj_id, StrictificationTensorProductMap]
    simp
    rw [StrictificationTensorProductMapTheta]
    ext A
    simp
    rw [cat_obj_id_app, cat_obj_id_app, NatTrans.id_app', NatTrans.id_app', Functor.map_id, Category.comp_id]
  map_comp F G := by
    apply StrictificationCatHom.ext
    simp
    rw [StrictificationTensorProductMap]
    simp
    rw [StrictificationTensorProductMapTheta]
    ext A
    simp
    rw [tensor_product_map_comp, NatTrans.vcomp_eq_comp, NatTrans.comp_app, StrictificationTensorProductMap, StrictificationTensorProductMap]
    simp
    rw [StrictificationTensorProductMapTheta, StrictificationTensorProductMapTheta]
    simp
    rw [←Category.assoc, ←NatTrans.vcomp_app', ←Functor.map_comp, ←NatTrans.vcomp_app', ←NatTrans.vcomp_eq_comp, ←NatTrans.vcomp_eq_comp, cat_hom_comp_app, cat_hom_comp_app]

def StrictificationUnitObject : StrictificationCatObj ℳ where
  F := 𝟭 ℳ
  η _ _ := by rw [Functor.id_obj, Functor.id_obj]

instance StrictificationStrictMonoidalCat : StrictMonoidalCategory (StrictificationCatObj ℳ) where
  tensorProduct := StrictificationTensorProduct ℳ
  unitObject := StrictificationUnitObject ℳ
  associator A B C := by

end Quantum
