module FOLsequent where

open import Data.String using (String)

open import Data.Empty

open import Data.Nat


open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary


open import Data.String using (String; _++_)

-- open import Data.Fin
-- open import Data.Fin.Subset
open import Data.List.Base as List using (List; []; _∷_; [_])
-- open import Data.Bool using () renaming (_∨_ to _∨B_)
open import Data.List.Any as LAny
open LAny.Membership-≡

data Term : Set where
  $_ : ℕ → Term
  Fun : String → List Term → Term

Const : String -> Term
Const n = Fun n []

data Formula : Set where
  _⟨_⟩ : String → List Term → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  _⟶_ : Formula → Formula → Formula
  ~_ : Formula → Formula
  All : (Term → Formula) → Formula
  Ex : (Term → Formula) → Formula

data Structure : Set where
  ∣_∣ : Formula → Structure
  _,,_ : Structure → Structure → Structure
  Ø : Structure


mutual
  FVt : Term → List ℕ
  FVt ($ x) = [ x ]
  FVt (Fun _ args) = FVlst args

  FVlst : List Term -> List ℕ
  FVlst [] = []
  FVlst (x ∷ xs) = (FVt x) List.++ (FVlst xs)

  FVf : Formula → List ℕ
  FVf (_ ⟨ lst ⟩) = FVlst lst
  FVf (f ∧ f₁) = FVf f List.++ FVf f₁
  FVf (f ∨ f₁) = FVf f List.++ FVf f₁
  FVf (f ⟶ f₁) = FVf f List.++ FVf f₁
  FVf (~ f) = FVf f
  FVf (All x) = FVf (x (Const ""))
  FVf (Ex x) = FVf (x (Const ""))

FV : Structure → List ℕ
FV ∣ f ∣ = FVf f
FV (s ,, t) = FV s List.++ FV t
FV Ø = []

_#_ : ℕ -> List ℕ -> Set
x # xs = x ∉ xs

∪ : List ℕ -> ℕ
∪ [] = 0
∪ (x ∷ xs) = x ⊔ (∪ xs)

∃fresh : List ℕ -> ℕ
∃fresh xs = suc (∪ xs)


open import Data.Sum
open import Data.Nat.Properties
-- _∨_ = _⊎_
------------------------------------------------------------------------------------

ℕ-meet-dist : ∀ {x y z : ℕ} -> (x ≤ y) ⊎ (x ≤ z) -> x ≤ y ⊔ z
ℕ-meet-dist {zero} x≤y⊎x≤z = z≤n
ℕ-meet-dist {suc x} {zero} {zero} (inj₁ ())
ℕ-meet-dist {suc x} {zero} {zero} (inj₂ ())
ℕ-meet-dist {suc x} {zero} {suc z} (inj₁ ())
ℕ-meet-dist {suc x} {zero} {suc z} (inj₂ sx≤sz) = sx≤sz
ℕ-meet-dist {suc x} {suc y} {zero} (inj₁ sx≤sy) = sx≤sy
ℕ-meet-dist {suc x} {suc y} {zero} (inj₂ ())
ℕ-meet-dist {suc x} {suc y} {suc z} (inj₁ (s≤s x≤y)) = s≤s (ℕ-meet-dist (inj₁ x≤y))
ℕ-meet-dist {suc x} {suc y} {suc z} (inj₂ (s≤s y≤z)) =
  s≤s (ℕ-meet-dist {_} {y} {z} (inj₂ y≤z))
------------------------------------------------------------------------------------

≤-refl : ∀ {x : ℕ} -> x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl
------------------------------------------------------------------------------------

∈-cons : ∀ {L} {x y : ℕ} -> x ∈ (y ∷ L) -> ¬(x ≡ y) -> x ∈ L
∈-cons {[]} (here refl) ¬x≡y = ⊥-elim (¬x≡y refl)
∈-cons {[]} (there ()) ¬x≡y
∈-cons {y ∷ L} {x} (here refl) ¬x≡y = ⊥-elim (¬x≡y refl)
∈-cons {y ∷ L} {x} (there x∈L) ¬x≡y = x∈L
------------------------------------------------------------------------------------

∃fresh-impl-spec' : ∀ x L -> x ∈ L -> x ≤ ∪ L
∃fresh-impl-spec' x [] ()
∃fresh-impl-spec' x (y ∷ L) x∈y∷L with x ≟ y
∃fresh-impl-spec' x (.x ∷ L) x∈y∷L | yes refl = ℕ-meet-dist {x} {x} (inj₁ ≤-refl)
∃fresh-impl-spec' x (y ∷ L) x∈y∷L | no ¬x≡y =
  ℕ-meet-dist {x} {y} (inj₂ (∃fresh-impl-spec' x L (∈-cons x∈y∷L ¬x≡y)))
------------------------------------------------------------------------------------

∃fresh-impl-spec'' : ∀ x L -> x ∈ L -> ¬ (x ≡ ∃fresh L)
∃fresh-impl-spec'' .(suc (∪ L)) L x∈L refl =
  1+n≰n {∪ L} (∃fresh-impl-spec' (suc (∪ L)) L x∈L)
------------------------------------------------------------------------------------

∃fresh-lemma : ∀ L -> ∃fresh L ∉ L
∃fresh-lemma L ∃freshL∈L =
  ∃fresh-impl-spec'' (∃fresh L) L ∃freshL∈L refl



data _⊢_ : Structure → Structure → Set where
  I : ∀ {A} → ∣ A ∣ ⊢ ∣ A ∣
  Cut : ∀ A {Γ Σ Δ Π} →
    Γ ⊢ (Δ ,, ∣ A ∣) → (∣ A ∣ ,, Σ) ⊢ Π →
    -----------------------------
         (Γ ,, Σ) ⊢ (Δ ,, Π)
  ∧L₁ : ∀ {Γ Δ A B} → (Γ ,, ∣ A ∣) ⊢ Δ → (Γ ,, ∣ A ∧ B ∣) ⊢ Δ
  ∧L₂ : ∀ {Γ Δ A B} → (Γ ,, ∣ B ∣) ⊢ Δ → (Γ ,, ∣ A ∧ B ∣) ⊢ Δ
  ∧R : ∀ {Γ Σ Δ Π A B} →
    Γ ⊢ (∣ A ∣ ,, Δ) → Σ ⊢ (∣ B ∣ ,, Π) →
    -----------------------------------
    (Γ ,, Σ) ⊢ (∣ A ∧ B ∣ ,, (Δ ,, Π))
  ∨R₁ : ∀ {Γ Δ A B} → Γ ⊢ (∣ A ∣ ,, Δ) → Γ ⊢ (∣ A ∨ B ∣ ,, Δ)
  ∨R₂ : ∀ {Γ Δ A B} → Γ ⊢ (∣ B ∣ ,, Δ) → Γ ⊢ (∣ A ∨ B ∣ ,, Δ)
  ∨L :  ∀ {Γ Σ Δ Π A B} →
    (Γ ,, ∣ A ∣) ⊢ Δ → (Σ ,, ∣ B ∣) ⊢ Π →
    -----------------------------------
    ((Γ ,, Σ) ,, ∣ A ∨ B ∣) ⊢ (Δ ,, Π)
  ⟶L : ∀ {Γ Σ Δ Π A B} →
    Γ ⊢ (∣ A ∣ ,, Δ) → (Σ ,, ∣ B ∣) ⊢ Π →
    -----------------------------------
    ((Γ ,, Σ) ,, ∣ A ⟶ B ∣) ⊢ (Δ ,, Π)
  ⟶R : ∀ {Γ Δ A B} → (Γ ,, ∣ A ∣) ⊢ (∣ B ∣ ,, Δ) → Γ ⊢ (∣ A ⟶ B ∣ ,, Δ)
  ~L : ∀ {Γ Δ A} → Γ ⊢ (∣ A ∣ ,, Δ) → (Γ ,, ∣ ~ A ∣) ⊢ Δ
  ~R : ∀ {Γ Δ A} → (Γ ,, ∣ A ∣) ⊢ Δ → Γ ⊢ (∣ ~ A ∣ ,, Δ)
  AllL : ∀ {Γ Δ A t} → (Γ ,, ∣ A t ∣) ⊢ Δ → (Γ ,, ∣ All A ∣) ⊢ Δ
  AllR : ∀ {Γ Δ A y} →
    Γ ⊢ (∣ A ($ y) ∣ ,, Δ) → (y-fresh : y # FV (Γ ,, Δ)) →
    ----------------------
    Γ ⊢ (∣ All A ∣ ,, Δ)
  ExL : ∀ {Γ Δ A y} →
    (Γ ,, ∣ A ($ y) ∣) ⊢ Δ → (y-fresh : y # FV (Γ ,, Δ)) →
    ----------------------
    (Γ ,, ∣ Ex A ∣) ⊢ Δ
  ExR : ∀ {Γ Δ A t} →
    Γ ⊢ (∣ A t ∣ ,, Δ) → Γ ⊢ (∣ Ex A ∣ ,, Δ)
  WL : ∀ {Γ Δ A} → Γ ⊢ Δ → (Γ ,, ∣ A ∣) ⊢ Δ
  WR : ∀ {Γ Δ A} → Γ ⊢ Δ → Γ ⊢ (∣ A ∣ ,, Δ)
  CL : ∀ {Γ Δ A} → (Γ ,, (∣ A ∣ ,, ∣ A ∣)) ⊢ Δ → (Γ ,, ∣ A ∣) ⊢ Δ
  CR : ∀ {Γ Δ A} → Γ ⊢ ((∣ A ∣ ,, ∣ A ∣) ,, Δ) → Γ ⊢ (∣ A ∣ ,, Δ)
  PL : ∀ {Γ₁ Γ₂ Δ A B} →
    ((Γ₁ ,, ∣ A ∣) ,, (∣ B ∣ ,, Γ₂)) ⊢ Δ →
    ------------------------------------
    ((Γ₁ ,, ∣ B ∣) ,, (∣ A ∣ ,, Γ₂)) ⊢ Δ
  PR : ∀ {Γ Δ₁ Δ₂ A B} →
    Γ ⊢ ((Δ₁ ,, ∣ A ∣) ,, (∣ B ∣ ,, Δ₂)) →
    ------------------------------------
    Γ ⊢ ((Δ₁ ,, ∣ B ∣) ,, (∣ A ∣ ,, Δ₂))
  AL₁ : ∀ {Γ₁ Γ₂ Γ₃ Δ} →
    ((Γ₁ ,, Γ₂) ,, Γ₃) ⊢ Δ →
    ----------------------
    (Γ₁ ,, (Γ₂ ,, Γ₃)) ⊢ Δ
  AL₂ : ∀ {Γ₁ Γ₂ Γ₃ Δ} →
    (Γ₁ ,, (Γ₂ ,, Γ₃)) ⊢ Δ →
    ----------------------
    ((Γ₁ ,, Γ₂) ,, Γ₃) ⊢ Δ
  AR₁ : ∀ {Γ Δ₁ Δ₂ Δ₃} →
    Γ ⊢ ((Δ₁ ,, Δ₂) ,, Δ₃) →
    ----------------------
    Γ ⊢ (Δ₁ ,, (Δ₂ ,, Δ₃))
  AR₂ : ∀ {Γ Δ₁ Δ₂ Δ₃} →
    Γ ⊢ (Δ₁ ,, (Δ₂ ,, Δ₃)) →
    ----------------------
    Γ ⊢ ((Δ₁ ,, Δ₂) ,, Δ₃)
  ØL₁ : ∀ {Γ Δ} → Γ ⊢ Δ → (Ø ,, Γ) ⊢ Δ
  ØL₂ : ∀ {Γ Δ} → (Ø ,, Γ) ⊢ Δ → Γ ⊢ Δ
  ØR₁ : ∀ {Γ Δ} → Γ ⊢ Δ → Γ ⊢ (Δ ,, Ø)
  ØR₂ : ∀ {Γ Δ} → Γ ⊢ (Δ ,, Ø) → Γ ⊢ Δ


simple : ∀ {P} -> ∣ All (λ x -> P ⟨ [ x ] ⟩) ∣ ⊢ ∣ All (λ y -> P ⟨ [ y ] ⟩) ∣
simple {P} = ØR₂ (AllR {y = y} (ØL₂ (AllL {t = $ y} (ØL₁ (ØR₁ I)))) y-fresh)
  where
    y = ∃fresh (FV (∣ All (λ x → P ⟨ [ x ] ⟩) ∣ ,, Ø))
    y-fresh = ∃fresh-lemma (FV (∣ All (λ x → P ⟨ [ x ] ⟩) ∣ ,, Ø))
