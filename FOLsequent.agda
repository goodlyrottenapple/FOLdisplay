module FOLsequent where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.String using (String)
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Any as LAny
open LAny.Membership-≡

data Term : Set where
  $ : ℕ → Term
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

-- data Structure : Set where
--   ∣_∣ : Formula → Structure
--   _,,_ : Structure → Structure → Structure
--   Ø : Structure


Structure = List Formula

mutual
  FVt : Term → List ℕ
  FVt ($ x) = [ x ]
  FVt (Fun _ args) = FVlst args

  FVlst : List Term -> List ℕ
  FVlst [] = []
  FVlst (x ∷ xs) = (FVt x) ++ (FVlst xs)

  FVf : Formula → List ℕ
  FVf (_ ⟨ lst ⟩) = FVlst lst
  FVf (f ∧ f₁) = FVf f ++ FVf f₁
  FVf (f ∨ f₁) = FVf f ++ FVf f₁
  FVf (f ⟶ f₁) = FVf f ++ FVf f₁
  FVf (~ f) = FVf f
  FVf (All x) = FVf (x (Const ""))
  FVf (Ex x) = FVf (x (Const ""))

FV : Structure → List ℕ
FV [] = []
FV (f ∷ l) = FVf f ++ FV l

_#_ : ℕ -> List ℕ -> Set
x # xs = x ∉ xs

∪ : List ℕ -> ℕ
∪ [] = 0
∪ (x ∷ xs) = x ⊔ (∪ xs)

∃# : List ℕ -> ℕ
∃# xs = suc (∪ xs)


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

∃#-lemma' : ∀ x L -> x ∈ L -> x ≤ ∪ L
∃#-lemma' x [] ()
∃#-lemma' x (y ∷ L) x∈y∷L with x ≟ y
∃#-lemma' x (.x ∷ L) x∈y∷L | yes refl = ℕ-meet-dist {x} {x} (inj₁ ≤-refl)
∃#-lemma' x (y ∷ L) x∈y∷L | no ¬x≡y =
  ℕ-meet-dist {x} {y} (inj₂ (∃#-lemma' x L (∈-cons x∈y∷L ¬x≡y)))
------------------------------------------------------------------------------------

∃#-lemma'' : ∀ x L -> x ∈ L -> ¬ (x ≡ ∃# L)
∃#-lemma'' .(suc (∪ L)) L x∈L refl =
  1+n≰n {∪ L} (∃#-lemma' (suc (∪ L)) L x∈L)
------------------------------------------------------------------------------------

∃#-lemma : ∀ L -> ∃# L ∉ L
∃#-lemma L ∃#L∈L = ∃#-lemma'' (∃# L) L ∃#L∈L refl


data _⊢_ : Structure → Structure → Set where
  I : ∀ {A} → [ A ] ⊢ [ A ]
  Cut : ∀ A {Γ Σ Δ Π} →
    Γ ⊢ (Δ ++ [ A ]) → ([ A ] ++ Σ) ⊢ Π →
    ------------------------------------
            (Γ ++ Σ) ⊢ (Δ ++ Π)
  ∧L₁ : ∀ {Γ Δ A B} → (Γ ++ [ A ]) ⊢ Δ → (Γ ++ [ A ∧ B ]) ⊢ Δ
  ∧L₂ : ∀ {Γ Δ A B} → (Γ ++ [ B ]) ⊢ Δ → (Γ ++ [ A ∧ B ]) ⊢ Δ
  ∧R : ∀ {Γ Σ Δ Π A B} →
    Γ ⊢ ([ A ] ++ Δ) → Σ ⊢ ([ B ] ++ Π) →
    -----------------------------------
    (Γ ++ Σ) ⊢ ([ A ∧ B ] ++ Δ ++ Π)
  ∨R₁ : ∀ {Γ Δ A B} → Γ ⊢ ([ A ] ++ Δ) → Γ ⊢ ([ A ∨ B ] ++ Δ)
  ∨R₂ : ∀ {Γ Δ A B} → Γ ⊢ ([ B ] ++ Δ) → Γ ⊢ ([ A ∨ B ] ++ Δ)
  ∨L :  ∀ {Γ Σ Δ Π A B} →
    (Γ ++ [ A ]) ⊢ Δ → (Σ ++ [ B ]) ⊢ Π →
    -----------------------------------
    (Γ ++ Σ ++ [ A ∨ B ]) ⊢ (Δ ++ Π)
  ⟶L : ∀ {Γ Σ Δ Π A B} →
    Γ ⊢ ([ A ] ++ Δ) → (Σ ++ [ B ]) ⊢ Π →
    ------------------------------------
    (Γ ++ Σ ++ [ A ⟶ B ]) ⊢ (Δ ++ Π)
  ⟶R : ∀ {Γ Δ A B} → (Γ ++ [ A ]) ⊢ ([ B ] ++ Δ) → Γ ⊢ ([ A ⟶ B ] ++ Δ)
  ~L : ∀ {Γ Δ A} → Γ ⊢ ([ A ] ++ Δ) → (Γ ++ [ ~ A ]) ⊢ Δ
  ~R : ∀ {Γ Δ A} → (Γ ++ [ A ]) ⊢ Δ → Γ ⊢ ([ ~ A ] ++ Δ)
  AllL : ∀ {Γ Δ A t} → (Γ ++ [ A t ]) ⊢ Δ → (Γ ++ [ All A ]) ⊢ Δ
  AllR : ∀ {Γ Δ A y} →
    Γ ⊢ ([ A ($ y) ] ++ Δ) → (y-fresh : y # FV (Γ ++ Δ)) →
    ----------------------
    Γ ⊢ ([ All A ] ++ Δ)
  ExL : ∀ {Γ Δ A y} →
    (Γ ++ [ A ($ y) ]) ⊢ Δ → (y-fresh : y # FV (Γ ++ Δ)) →
    ----------------------
    (Γ ++ [ Ex A ]) ⊢ Δ
  ExR : ∀ {Γ Δ A t} → Γ ⊢ ([ A t ] ++ Δ) → Γ ⊢ ([ Ex A ] ++ Δ)
  WL : ∀ {Γ Δ A} → Γ ⊢ Δ → (Γ ++ [ A ]) ⊢ Δ
  WR : ∀ {Γ Δ A} → Γ ⊢ Δ → Γ ⊢ ([ A ] ++ Δ)
  CL : ∀ {Γ Δ A} → (Γ ++ [ A ] ++ [ A ]) ⊢ Δ → (Γ ++ [ A ]) ⊢ Δ
  CR : ∀ {Γ Δ A} → Γ ⊢ ([ A ] ++ [ A ] ++ Δ) → Γ ⊢ ([ A ] ++ Δ)
  PL : ∀ {Γ₁ Γ₂ Δ A B} →
    (Γ₁ ++ [ A ] ++ [ B ] ++ Γ₂) ⊢ Δ →
    ------------------------------------
    (Γ₁ ++ [ B ] ++ [ A ] ++ Γ₂) ⊢ Δ
  PR : ∀ {Γ Δ₁ Δ₂ A B} →
    Γ ⊢ (Δ₁ ++ [ A ] ++ [ B ] ++ Δ₂) →
    ------------------------------------
    Γ ⊢ (Δ₁ ++ [ B ] ++ [ A ] ++ Δ₂)


PL2 : ∀ {A B Δ} -> (A ∷ [ B ]) ⊢ Δ → (B ∷ [ A ]) ⊢ Δ
PL2 {A} {B} A,B⊢Δ = PL {[]} {[]} {_} {A} {B} A,B⊢Δ

PR2 : ∀ {A B Γ} -> Γ ⊢ (A ∷ [ B ]) → Γ ⊢ (B ∷ [ A ])
PR2 {A} {B} Γ⊢A,B = PR {_} {[]} {[]} {A} {B} Γ⊢A,B


_>>_ : ∀ {A B : Set} -> (A → B) -> A -> B
A→B >> A = A→B A

open import Data.Product
_>>₂_ : ∀ {A B C : Set} -> (A → B → C) -> A × B -> C
A→B→C >>₂ (A , B) = A→B→C A B

infixr 4 _>>_
infixr 4 _>>₂_

lemma : ∀ {A B C} -> [] ⊢ [ (A ⟶ (B ∨ C)) ⟶ (((B ⟶ (~ A)) ∧ (~ C)) ⟶ (~ A)) ]
lemma {A} {B} {C} = ⟶R >> ⟶R >> PL2 >> CR >> ⟶L {[]} {[ (B ⟶ (~ A)) ∧ (~ C) ]} {[ ~ A ]} {[ ~ A ]} >>₂
  (PR2 >> ~R >> I) ,
  PL2 >> CL {[ B ∨ C ]} {A = (B ⟶ (~ A)) ∧ (~ C)} >> ∧L₂ {(B ∨ C) ∷ [ (B ⟶ (~ A)) ∧ (~ C) ]}
    >> PL {[ B ∨ C ]} {[]} >> ∧L₁ {(B ∨ C) ∷ [ ~ C ]} >> ⟶L {(B ∨ C) ∷ [ ~ C ]} {[]} {[]} >>₂
      (~L {[ B ∨ C ]} >> PR2 >> ∨L {[]} {[]} {[ B ]} >>₂ I , I) ,
      I

lemma₁ : ∀ {P} → [ All (λ x → P ⟨ [ x ] ⟩) ] ⊢ [ All (λ y → P ⟨ [ y ] ⟩) ]
lemma₁ {P} = AllR {y = y} (AllL {[]} {t = $ y} I) y-fresh
  where
    y = ∃# (FV [ All (λ x → P ⟨ [ x ] ⟩) ])
    y-fresh = ∃#-lemma (FV [ All (λ x → P ⟨ [ x ] ⟩) ])

AllR# : ∀ {Γ Δ A} → Γ ⊢ ([ A ($ (∃# (FV (Γ ++ Δ)))) ] ++ Δ) → Γ ⊢ ([ All A ] ++ Δ)
AllR# {Γ} {Δ} Γ⊢[y/x]A,Δ = AllR Γ⊢[y/x]A,Δ (∃#-lemma (FV (Γ ++ Δ)))

ExL# : ∀ {Γ Δ A} → (Γ ++ [ A ($ (∃# (FV (Γ ++ Δ)))) ]) ⊢ Δ → (Γ ++ [ Ex A ]) ⊢ Δ
ExL# {Γ} {Δ} Γ,[y/x]A⊢Δ = ExL {Γ} Γ,[y/x]A⊢Δ (∃#-lemma (FV (Γ ++ Δ)))


lemma₂ : ∀ {P} →
  [ Ex (λ y → All (λ x → P ⟨ x ∷ [ y ] ⟩)) ] ⊢ [ All (λ x → Ex (λ y → P ⟨ x ∷ [ y ] ⟩)) ]
lemma₂ {P} = AllR# >> ExL# {[]} >> ExR >> AllL {[]} >> I
