module FOLdisplay where

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



Name : Set
Name = String


insert : ℕ → List ℕ → List ℕ
insert n List.[] = n ∷ []
insert n (x ∷ l) with n ≟ x
insert n (.n ∷ l) | yes refl = n ∷ l
insert n (x ∷ l) | no n≠x with n ≤? x
insert n (x ∷ l) | no n≠x | yes n<x = n ∷ x ∷ l
insert n (x ∷ l) | no n≠x | no n>x = x ∷ insert n l


sortRemDups : List ℕ → List ℕ
sortRemDups [] = []
sortRemDups (x ∷ xs) = insert x (sortRemDups xs)

union : List ℕ → List ℕ → List ℕ
union [] ys = ys
union (x ∷ xs) ys = insert x (union xs ys)


remove : ℕ → List ℕ → List ℕ
remove n [] = []
remove n (x ∷ xs) with n Data.Nat.≟ x
remove n (.n ∷ xs) | yes refl = xs
remove n (x ∷ xs) | no _ = x ∷ remove n xs


remove-rewrite : ∀ x {xs} -> remove x (x ∷ xs) ≡ xs
remove-rewrite x with x ≟ x
remove-rewrite x | yes refl = refl
remove-rewrite x | no x≠x = ⊥-elim (x≠x refl)



-- xs \\ ys
diff : List ℕ → List ℕ → List ℕ
diff xs [] = xs
diff xs (x ∷ ys) = diff (remove x xs) ys

--
-- mutual
--   data TermT : List ℕ -> Set where
--     VarT : (n : ℕ) → TermT [ n ]
--     ConstT : Name → TermT []
--     FunT : ∀ {xs} -> Name → (TermList xs) → TermT xs
--   -- [[[_]]]T_ : List (Term × ℕ) → Term → Term
--   data TermList : List ℕ -> Set where
--     []T : TermList []
--     _∷T_ : ∀ {xs ys} (t : TermT xs) (ts : TermT ys) -> TermList (union xs ys)
--
--   data SubstList : List ℕ -> Set where
--     []S : SubstList []
--     _/_∷S_ : ∀ {xs ys} (t : TermT xs) (x : ℕ) (ts : TermT ys) -> SubstList (union xs (remove x ys))



data Term : Set where
  Var : ℕ → Term
  Const : Name → Term
  Fun : Name → List Term → Term
  -- [[_/_]]_ : Term → ℕ → Term → Term
  [[[_]]]_ : List (Term × ℕ) → Term → Term

mutual
  data _⊢≡_ : Term → Term → Set where
    atom : ∀ {n} → Var n ⊢≡ Var n
    atomC : ∀ {n} → Const n ⊢≡ Const n
    funEq : ∀ {n arg1 arg2} → arg1 ≡ₗ arg2 → Fun n arg1 ⊢≡ Fun n arg2
    -- subMon : ∀ {substs X Y} → X ⊢≡ Y → ([[[ substs ]]] X) ⊢≡ ([[[ substs ]]] Y) -- this rule is derivable
    sub[]R : ∀ {X Y} → X ⊢≡ Y → X ⊢≡ ([[[ [] ]]] Y)
    sub[]L : ∀ {X Y} → X ⊢≡ Y → ([[[ [] ]]] X) ⊢≡ Y
    subAtomEqR : ∀ {x t lst X} → X ⊢≡ ([[[ lst ]]] t) → X ⊢≡ ([[[ (t , x) ∷ lst ]]] (Var x))
    subAtomEqL : ∀ {x t lst Y} → ([[[ lst ]]] t) ⊢≡ Y → ([[[ (t , x) ∷ lst ]]] (Var x)) ⊢≡ Y

    subAtomNeqR : ∀ {x y t lst X} → X ⊢≡ ([[[ lst ]]] (Var x)) → x ≢ y → X ⊢≡ ([[[ (t , y) ∷ lst ]]] (Var x))
    subAtomNeqL : ∀ {x y t lst Y} → ([[[ lst ]]] (Var x)) ⊢≡ Y → x ≢ y → ([[[ (t , y) ∷ lst ]]] (Var x)) ⊢≡ Y

    subAtomCR : ∀ {n lst X} → X ⊢≡ (Const n) → X ⊢≡ ([[[ lst ]]] (Const n))
    subAtomCL : ∀ {n lst Y} → (Const n) ⊢≡ Y → ([[[ lst ]]] (Const n)) ⊢≡ Y

    subFunR : ∀ {n arg lst X} → X ⊢≡ (Fun n (List.map ([[[_]]]_ lst) arg)) → X ⊢≡ ([[[ lst ]]] (Fun n arg))
    subFunL : ∀ {n arg lst Y} → (Fun n (List.map ([[[_]]]_ lst) arg)) ⊢≡ Y → ([[[ lst ]]] (Fun n arg)) ⊢≡ Y

    subConsR : ∀ {lst lst' X Y} → X ⊢≡ ([[[ lst List.++ lst' ]]] Y) → X ⊢≡ ([[[ lst' ]]] ([[[ lst ]]] Y))
    subConsL : ∀ {lst lst' X Y} → ([[[ lst List.++ lst' ]]] X) ⊢≡ Y → ([[[ lst' ]]] ([[[ lst ]]] X)) ⊢≡ Y

  data _≡ₗ_ : List Term → List Term → Set where
    []≡ : [] ≡ₗ []
    _∷≡_ : {xs : List Term} {ys : List Term} {t1 t2 : Term} → t1 ⊢≡ t2 → xs ≡ₗ ys → (t1 ∷ xs) ≡ₗ (t2 ∷ ys)




-- open import Data.Maybe using (Maybe; just; nothing; monad)
--
-- open import Category.Monad using (RawMonad)
-- open import Agda.Primitive as P
--
-- open RawMonad (monad {P.lzero}) using (_>>=_;return)
-- open Category.Monad.rawMonad
open import Data.String using () renaming (_≟_ to _≟S_)


data Term' : Set where
  Var' : ℕ → Term'
  Const' : Name → Term'
  Fun' : Name → List Term' → Term'

mutual
  data TTerm : List ℕ -> Set where
    TVar : (n : ℕ) → TTerm [ n ]
    TConst : Name → TTerm []
    TFun : ∀ {xs} -> Name → TTermList xs → TTerm xs

  data TTermList : List ℕ -> Set where
    []T : TTermList []
    _∷T_ : ∀ {xs ys} (t : TTerm xs) (ts : TTermList ys) -> TTermList (union xs ys)


open import Relation.Nullary.Decidable
open import Relation.Binary.Core

open import Data.List.Any as LAny
open LAny.Membership-≡

∈-∷-elim : ∀ {A : Set} {x : A} (y : A) xs -> ¬(x ≡ y) -> y ∈ x ∷ xs -> y ∈ xs
∈-∷-elim x [] x≠y (here refl) = ⊥-elim (x≠y refl)
∈-∷-elim y [] _ (there ())
∈-∷-elim x (x₁ ∷ xs) x≠y (here refl) = ⊥-elim (x≠y refl)
∈-∷-elim y (x₁ ∷ xs) _ (there y∈x∷xs) = y∈x∷xs


_∈ℕ?_ : Decidable {A = ℕ} (_∈_)
x ∈ℕ? [] = no (λ ())
x ∈ℕ? (x' ∷ xs) with x ≟ x'
x ∈ℕ? (.x ∷ xs) | yes refl = yes (here refl)
x ∈ℕ? (x' ∷ xs) | no x≠x' with x ∈ℕ? xs
x ∈ℕ? (x' ∷ xs) | no x≠x' | yes x∈xs = yes (there x∈xs)
x ∈ℕ? (x' ∷ xs) | no x≠x' | no x∉xs = no (λ x∈x'∷xs → x∉xs (∈-∷-elim x xs (λ x'≡x → x≠x' (sym x'≡x)) x∈x'∷xs))




-- subTaux : List ℕ -> ℕ -> List ℕ -> List ℕ
-- subTaux xs x ys with x ∈ℕ? ys
-- subTaux xs x ys | yes _ = union xs (remove x ys)
-- subTaux xs x ys | no _ = ys

-- mutual
--   subT : ∀ {ts ys} → TTerm ts → (x : ℕ) -> TTerm ys → TTerm (subTaux ts x ys)
--   subT t x (TVar x') with x ≟ x'
--   subT t .x' (TVar x') | yes refl rewrite remove-rewrite x' {[]} = {! t'  !}
--   ... | no _ = (TVar x')
--   subT _ _ (TConst n) = TConst n
--   subT t x (TFun n args) = TFun n (subTList t x args)
--
--   subTList : ∀ {ts ys} → TTerm ts → (x : ℕ) -> TTermList ys → TTermList (subTaux ts x ys)
--   subTList _ _ []T = []T
--   subTList {ts} t x (_∷T_ {xs} {ys} a args) = rec
--     where
--       a' : TTerm (subTaux ts x xs)
--       a' = subT t x a
--
--       args' : TTermList (subTaux ts x ys)
--       args' = subTList t x args
--
--       ≡-subTaux : ∀ x xs ys -> subTaux ts x (union xs ys) ≡ union (subTaux ts x xs) (subTaux ts x ys)
--       ≡-subTaux _ [] _ = refl
--       ≡-subTaux x (x' ∷ xs) ys = {!   !}
--
--       rec : TTermList (subTaux ts x (union xs ys))
--       rec rewrite ≡-subTaux x xs ys = a' ∷T args'
--
--     --subT x t' t ∷T subTList x t' l
--

TTerm→Term : ∀ {xs} -> TTerm xs -> Term
TTerm→Term (TVar n) = Var n
TTerm→Term (TConst c) = Const c
TTerm→Term (TFun n args) = Fun n (TTermList→ListTerm args)
  where
    TTermList→ListTerm : ∀ {xs} -> TTermList xs -> List Term
    TTermList→ListTerm []T = []
    TTermList→ListTerm (_∷T_ {_} {ys} t ts) = (TTerm→Term t) ∷ (TTermList→ListTerm {ys} ts)

mutual
  sub : ℕ → Term' → Term' → Term'
  sub x t' (Var' x') with x ≟ x'
  ... | yes _ = t'
  ... | no _ = (Var' x')
  sub x t' (Const' n) = Const' n
  sub x t' (Fun' n args) = Fun' n (subList x t' args)

  subList : ℕ → Term' → List Term' → List Term'
  subList x t' [] = []
  subList x t' (t ∷ l) = sub x t' t ∷ subList x t' l


mutual
  Term→Term' : Term → Term'
  Term→Term' (Var x) = Var' x
  Term→Term' (Const c) = Const' c
  Term→Term' (Fun n args) = Fun' n (LTerm→LTerm' args)
  Term→Term' ([[[ lst ]]] t) = STerm lst (Term→Term' t)

  LTerm→LTerm' : List Term → List Term'
  LTerm→LTerm' [] = []
  LTerm→LTerm' (x ∷ l) = Term→Term' x ∷ LTerm→LTerm' l

  STerm : List (Term × ℕ) → Term' → Term'
  STerm [] t = t
  STerm ((t' , x) ∷ lst) t = STerm lst (sub x (Term→Term' t') t)



mutual
  ⊢≡symm : ∀ {t1 t2 : Term} → t1 ⊢≡ t2 → t2 ⊢≡ t1
  ⊢≡symm atom = atom
  ⊢≡symm atomC = atomC
  ⊢≡symm (funEq x) = funEq (≡ₗsymm x)
  ⊢≡symm (sub[]R {Y = Y} t1⊢≡t2) = sub[]L (⊢≡symm t1⊢≡t2)
  ⊢≡symm (sub[]L {X = X} t1⊢≡t2) = sub[]R (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subAtomEqR {t = t} {lst} t1⊢≡t2) = subAtomEqL (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subAtomEqL {t = t} {lst} t1⊢≡t2) = subAtomEqR (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subAtomNeqR {x = x} t1⊢≡t2 x₁) = subAtomNeqL (⊢≡symm t1⊢≡t2) x₁
  ⊢≡symm (subAtomNeqL {x = x} t1⊢≡t2 x₁) = subAtomNeqR (⊢≡symm t1⊢≡t2) x₁
  ⊢≡symm (subAtomCR {n = n} t1⊢≡t2) = subAtomCL (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subAtomCL t1⊢≡t2) = subAtomCR (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subFunR t1⊢≡t2) = subFunL (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subFunL t1⊢≡t2) = subFunR (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subConsR t1⊢≡t2) = subConsL (⊢≡symm t1⊢≡t2)
  ⊢≡symm (subConsL t1⊢≡t2) = subConsR (⊢≡symm t1⊢≡t2)

  ≡ₗsymm : ∀ {arg1 arg2} → arg1 ≡ₗ arg2 → arg2 ≡ₗ arg1
  ≡ₗsymm []≡ = []≡
  ≡ₗsymm (x ∷≡ arg1≡ₗarg2) = (⊢≡symm x) ∷≡ (≡ₗsymm arg1≡ₗarg2)



≡-Fun-nm : ∀ {n n' args args'} → Fun' n args ≡ Fun' n' args' → n ≡ n'
≡-Fun-nm refl = refl

≡-Fun-args : ∀ {n args args'} → Fun' n args ≡ Fun' n args' → args ≡ args'
≡-Fun-args refl = refl

Fun-args-≡ : ∀ {n args args'} → args ≡ args' → Fun' n args ≡ Fun' n args'
Fun-args-≡ refl = refl




substFun≡aux : ∀ {n} lst args → STerm lst (Fun' n args) ≡ Fun' n (List.map (STerm lst) args)
substFun≡aux [] args = Fun-args-≡ (aux args)
  where
    aux : ∀ args → args ≡ List.map (STerm []) args
    aux [] = refl
    aux (a ∷ args) = cong (_∷_ a) (aux args)
substFun≡aux {n} ((t , x) ∷ lst) args = PropEq.trans (substFun≡aux {n} lst (subList x (Term→Term' t) args)) (Fun-args-≡ (aux lst x t args))
  where
    aux : ∀ lst x t args → List.map (STerm lst) (subList x (Term→Term' t) args) ≡ List.map (STerm ((t , x) ∷ lst)) args
    aux lst x t [] = refl
    aux lst x t (x' ∷ args) = cong (_∷_ (STerm lst (sub x (Term→Term' t) x'))) (aux lst x t args)

substFun≡ : ∀ {n} args lst → Term→Term' ([[[ lst ]]] Fun n args) ≡ Fun' n (LTerm→LTerm' (List.map ([[[_]]]_ lst) args))
substFun≡ [] [] = refl
substFun≡ [] (s ∷ lst) = substFun≡ [] lst
substFun≡ (a ∷ args) [] = Fun-args-≡ (cong (_∷_ (Term→Term' a)) (LTerm[]Subst args))
  where
    LTerm[]Subst : ∀ args → LTerm→LTerm' args ≡ LTerm→LTerm' (List.map ([[[_]]]_ []) args)
    LTerm[]Subst [] = refl
    LTerm[]Subst (a ∷ args) = cong (_∷_ (Term→Term' a)) (LTerm[]Subst args)
substFun≡ (a ∷ args) ((t , x) ∷ lst) = PropEq.trans
  (substFun≡aux lst (subList x (Term→Term' t) (LTerm→LTerm' (a ∷ args))))
  (Fun-args-≡ (aux (a ∷ args)))
  where
    aux : ∀ args {lst x t} → List.map (STerm lst) (subList x (Term→Term' t) (LTerm→LTerm' args)) ≡ LTerm→LTerm' (List.map ([[[_]]]_ ((t , x) ∷ lst)) args)
    aux [] = refl
    aux (a ∷ args) {lst} {x} {t} = cong (_∷_ (STerm lst (sub x (Term→Term' t) (Term→Term' a)))) (aux args)


++[]-id : ∀ {a} {A : Set a} (lst : List A) → lst List.++ [] ≡ lst
++[]-id [] = refl
++[]-id (x ∷ xs) = cong (_∷_ x) (++[]-id xs)


substSubst≡ : ∀ {lst lst' t} → Term→Term' ([[[ lst ]]] ([[[ lst' ]]] t)) ≡ Term→Term' ([[[ lst' List.++ lst ]]] t)
substSubst≡ {[]} {lst'} rewrite ++[]-id lst' = refl
substSubst≡ {(t , x₂) ∷ lst} {[]} = refl
substSubst≡ {(t , x) ∷ lst} {(t' , x') ∷ lst'} {t''} = substSubst≡ {(t , x) ∷ lst} {lst'} {[[[ [ (t' , x') ]  ]]] t''}

subsConst≡ : ∀ {lst c} → Term→Term' ([[[ lst ]]] (Const c)) ≡ Const' c
subsConst≡ {[]} = refl
subsConst≡ {_ ∷ lst} {c} = subsConst≡ {lst} {c}


open import Data.List.Properties

substTac : (t1 : Term) → (t2 : Term) → {_ : Term→Term' t1 ≡ Term→Term' t2} → t1 ⊢≡ t2
{-# TERMINATING #-}
substTac (Var x) (Var .x) {refl} = atom
substTac (Var _) (Const _) {()}
substTac (Var _) (Fun _ _) {()}

substTac (Const _) (Var _) {()}
substTac (Const c) (Const .c) {refl} = atomC
substTac (Const _) (Fun _ _) {()}

substTac (Fun _ _) (Var _) {()}
substTac (Fun _ _) (Const _) {()}
substTac (Fun n args) (Fun n' args') with n ≟S n'
substTac (Fun n []) (Fun .n []) | yes refl = funEq []≡
substTac (Fun n []) (Fun .n (_ ∷ _)) {()} | yes refl
substTac (Fun n (x ∷ args)) (Fun .n []) {()} | yes refl
substTac (Fun n (t ∷ args)) (Fun .n (t' ∷ args')) {eq} | yes refl with
  substTac t t' {proj₁ (∷-injective (≡-Fun-args eq))} |
  substTac (Fun n args) (Fun n args') {Fun-args-≡ (proj₂ (∷-injective (≡-Fun-args eq)))}
substTac (Fun n (t ∷ args)) (Fun .n (t' ∷ args')) | yes refl | t⊢≡t' | funEq args≡ₗargs' = funEq (t⊢≡t' ∷≡ args≡ₗargs')
substTac (Fun n args) (Fun n' args') {eq} | no ¬p = ⊥-elim (¬p (≡-Fun-nm eq))

substTac t1 ([[[ [] ]]] t2) {eq} = sub[]R (substTac t1 t2 {eq})
substTac t1 ([[[ (t , x') ∷ lst ]]] Var x) with x ≟ x'
substTac t1 ([[[ (t , x') ∷ lst ]]] Var .x') {eq} | yes refl =
  subAtomEqR (substTac t1 ([[[ lst ]]] t) {eq' {x'} {Term→Term' t1} {t} {lst} eq}) -- agda doesnt like this call because it doesnt get structurally smaller, but its fine...
  where
    eq' : ∀ {x t t' lst} → t ≡ Term→Term' (([[[ (t' , x) ∷ lst ]]] Var x)) → t ≡ Term→Term' ([[[ lst ]]] t')
    eq' {x} refl with x ≟ x
    eq' {x} refl | yes _ = refl
    eq' {x} refl | no ¬p = ⊥-elim (¬p refl)
substTac t1 ([[[ (t , x') ∷ lst ]]] Var x) {eq} | no ¬p = subAtomNeqR (substTac t1 ([[[ lst ]]] (Var x)) {eq' {x} {x'} {Term→Term' t1} {t} {lst} eq ¬p}) ¬p
  where
    eq' : ∀ {x x' t t' lst} → t ≡ Term→Term' (([[[ (t' , x') ∷ lst ]]] Var x)) → x ≢ x' → t ≡ Term→Term' ([[[ lst ]]] Var x)
    eq' {x} {x'} refl x≠x' with x' ≟ x
    eq' {x} {.x} refl x≠x' | yes refl = ⊥-elim (x≠x' refl)
    eq' {x} {x'} refl x≠x' | no ¬p = refl
substTac t1 ([[[ x ∷ lst ]]] Const c) {eq} = subAtomCR (substTac t1 (Const c) {PropEq.trans eq (subsConst≡ {x ∷ lst} {c})})
substTac t1 ([[[ x ∷ lst ]]] Fun n args) {eq} = subFunR (substTac t1 (Fun n (List.map ([[[_]]]_ (x ∷ lst)) args)) {PropEq.trans eq (substFun≡ args (x ∷ lst))})

substTac t1 ([[[ x ∷ lst ]]] ([[[ lst' ]]] t2)) {eq} =
  subConsR (substTac t1 ([[[ lst' List.++ x ∷ lst ]]] t2) {PropEq.trans eq (substSubst≡ {x ∷ lst} {lst'} {t2})})

substTac ([[[ lst ]]] t1) t2 {eq} = ⊢≡symm (substTac t2 ([[[ lst ]]] t1) {sym eq}) -- adga doesn't like this, but it should be fine...



⊢≡-≡ : ∀ {X Y} → X ⊢≡ Y → Term→Term' X ≡ Term→Term' Y
⊢≡-≡ atom = refl
⊢≡-≡ atomC = refl
⊢≡-≡ (funEq x) = Fun-args-≡ (≡ₗ→≡ x)
  where
    ∷-≡ : ∀ {a} {A : Set a} {x y : A} {xs ys} → x ≡ y → xs ≡ ys → x ∷ xs ≡ y ∷ ys
    ∷-≡ refl refl = refl

    ≡ₗ→≡ : ∀ {arg1 arg2} → arg1 ≡ₗ arg2 → (LTerm→LTerm' arg1) ≡ (LTerm→LTerm' arg2)
    ≡ₗ→≡ []≡ = refl
    ≡ₗ→≡ (t1⊢≡t2 ∷≡ ≡ₗ) = ∷-≡ (⊢≡-≡ t1⊢≡t2) (≡ₗ→≡ ≡ₗ)
⊢≡-≡ (sub[]R X⊢≡Y) = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (sub[]L X⊢≡Y) = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (subAtomEqR {x} X⊢≡Y) with x ≟ x
⊢≡-≡ (subAtomEqR {x} X⊢≡Y) | yes p = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (subAtomEqR {x} X⊢≡Y) | no ¬p = ⊥-elim (¬p refl)
⊢≡-≡ (subAtomEqL {x} X⊢≡Y) with x ≟ x
⊢≡-≡ (subAtomEqL {x} X⊢≡Y) | yes p = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (subAtomEqL {x} X⊢≡Y) | no ¬p = ⊥-elim (¬p refl)
⊢≡-≡ (subAtomNeqR {x} {y} X⊢≡Y x₁) with y ≟ x
⊢≡-≡ (subAtomNeqR {x} {.x} X⊢≡Y x₁) | yes refl = ⊥-elim (x₁ refl)
⊢≡-≡ (subAtomNeqR {x} {y} X⊢≡Y x₁) | no ¬p = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (subAtomNeqL {x} {y} X⊢≡Y x₁) with y ≟ x
⊢≡-≡ (subAtomNeqL {x} {.x} X⊢≡Y x₁) | yes refl = ⊥-elim (x₁ refl)
⊢≡-≡ (subAtomNeqL {x} {y} X⊢≡Y x₁) | no ¬p = ⊢≡-≡ X⊢≡Y
⊢≡-≡ (subAtomCR {c} {lst} X⊢≡Y) = PropEq.trans (⊢≡-≡ X⊢≡Y) (sym (subsConst≡ {lst} {c}))
⊢≡-≡ (subAtomCL {c} {lst} X⊢≡Y) = PropEq.trans (subsConst≡ {lst} {c}) (⊢≡-≡ X⊢≡Y)
⊢≡-≡ (subFunR {n} {args} {lst} X⊢≡Y) = PropEq.trans (⊢≡-≡ X⊢≡Y) (sym (substFun≡ {n} args lst))
⊢≡-≡ (subFunL {n} {args} {lst} X⊢≡Y) = PropEq.trans (substFun≡ {n} args lst) (⊢≡-≡ X⊢≡Y)
⊢≡-≡ (subConsR {lst} {lst'} {_} {Y} X⊢≡Y) = PropEq.trans (⊢≡-≡ X⊢≡Y) (sym (substSubst≡ {lst'} {lst} {Y}))
⊢≡-≡ (subConsL {lst} {lst'} {X} X⊢≡Y) = PropEq.trans (substSubst≡ {lst'} {lst} {X}) (⊢≡-≡ X⊢≡Y)

mutual
  ⊢≡atom : ∀ {t} → t ⊢≡ t
  ⊢≡atom {Var x} = atom
  ⊢≡atom {Const x} = atomC
  ⊢≡atom {Fun x x₁} = funEq ≡ₗatom
    where
      ≡ₗatom : ∀ {xs} → xs ≡ₗ xs
      ≡ₗatom {[]} = []≡
      ≡ₗatom {x ∷ xs} = ⊢≡atom ∷≡ ≡ₗatom
  ⊢≡atom {[[[ x ]]] t} = ⊢≡subMon ⊢≡atom


  ⊢≡subMon : ∀ {sub X Y} → X ⊢≡ Y → ([[[ sub ]]] X) ⊢≡ ([[[ sub ]]] Y)
  ⊢≡subMon {sub} {X} {Y} X⊢≡Y = substTac ([[[ sub ]]] X) ([[[ sub ]]] Y) {mon {sub} {Term→Term' X} {Term→Term' Y} (⊢≡-≡ X⊢≡Y)}
    where
      mon : ∀ {sub X Y} → X ≡ Y → STerm sub X ≡ STerm sub Y
      mon refl = refl


-- data _∈_ : ℕ → List ℕ → Set where
--   here : ∀ {x xs} → x ∈ (x ∷ xs)
--   there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)
--
-- data _⊆_ : List ℕ → List ℕ → Set where
--   nil : ∀ {xs} → [] ⊆ xs
--   cons : ∀ {x xs ys} → x ∈ ys → xs ⊆ ys → (x ∷ xs) ⊆ ys
--
-- _∉_ : ℕ → List ℕ → Set
-- n ∉ ns = ¬ (n ∈ ns)
--
-- _⊈_ : List ℕ → List ℕ → Set
-- xs ⊈ ys = ¬ (xs ⊆ ys)


mutual
  FV : Term' → List ℕ
  FV (Var' x) = [ x ]
  FV (Const' _) = []
  FV (Fun' _ args) = FVs args

  FVs : List Term' → List ℕ
  FVs [] = []
  FVs (t ∷ ts) = union (FV t) (FVs ts)




data Formula : List ℕ → Set where
  _⟨_⟩ : Name → ∀ {xs} (ts : TTermList xs) → Formula xs
  _∧_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  _∨_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  _⟶_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  ∘ : ∀ {ns} v → Formula ns → {v∉ : v ∉ ns} → Formula (insert v ns)
  -- [_/_] : ∀ {y ns} → Term → (x : ℕ) → {x∈ : x ∈ ns} → {y⊆ : y ⊆ ns} → {x≠y : [ x ] ≢ y} → Formula ns → Formula (remove x ns)
  -- [_//_] : ∀ {y ns} → Term y → (x : ℕ) → {x⊆ : x ∈ ns} → {y⊈ : y ⊈ ns} → {x≠y : [ x ] ≢ y} → Formula ns → Formula (union y (remove x ns))
  All : ∀ {ns} v → Formula ns → Formula (remove v ns)
  Ex : ∀ {ns} v → Formula ns → Formula (remove v ns)


data Structure : List ℕ → Set where
  ∣_∣ : ∀ {n} → Formula n → Structure n
  _,_ : ∀ {n m} → Structure n → Structure m → {n≡m : n ≡ m} -> Structure n
  _>>_ : ∀ {n m} → Structure n → Structure m → {n≡m : n ≡ m} → Structure n
  _<<_ : ∀ {n m} → Structure n → Structure m → {n≡m : n ≡ m} → Structure n
  I : ∀ {n} → Structure n
  ○ : ∀ {n} v → Structure n → {v∉ : v ∉ n} → Structure (insert v n)
  Q : ∀ {n} v → Structure n → Structure (remove v n)


data _⊢_ : ∀ {n} → Structure n → Structure n → Set where
  atom : ∀ {n xs} {ts us : TTermList xs} →
    ∣ n ⟨ ts ⟩ ∣ ⊢ ∣ n ⟨ us ⟩ ∣
  allR : ∀ {x n X Y} →
    Y ⊢ Q {n} x ∣ X ∣ →
    -------------------
    Y ⊢ ∣ All {n} x X ∣
  allL : ∀ {x n X Y} →
            ∣ Y ∣ ⊢ ∣ X ∣ →
    -------------------------------
    ∣ All {n} x Y ∣ ⊢ Q {n} x ∣ X ∣

open import Data.Unit as Unit using (⊤)
open import Data.Nat.Properties as Propℕ

_≤'?_ : Decidable _≤′_
x ≤'? y with x ≤? y
x ≤'? y | yes p = yes (≤⇒≤′ p)
x ≤'? y | no ¬p = no (λ x₁ → ¬p (≤′⇒≤ x₁))

-- mutual
--   data OList : Set where
--     []O : OList
--     _∷O_ : (x : ℕ) -> (xs : OList) -> {x< : isLess x xs} -> OList
--
--   isLess : ℕ -> OList -> Set
--   isLess x []O = ⊤
--   isLess x (y ∷O ol) with x ≤'? y
--   isLess x (.x ∷O ol) | yes ≤′-refl = ⊥
--   isLess x (.(suc _) ∷O ol) | yes (≤′-step _) = ⊤
--   isLess x (y ∷O ol) | no _ = ⊥
--
--
--
-- mutual
--   data IsLess : ℕ -> OList -> Set where
--     nil : ∀ {x} -> IsLess x []O
--     cons : ∀ {x x' xs} -> x < x' -> (x'<xs : IsLess x' xs) -> IsLess x ((x' ∷O xs) {IsLess→isLess x'<xs})
--
--   IsLess→isLess : ∀ {x xs} -> IsLess x xs -> isLess x xs
--   IsLess→isLess nil = ⊤.tt
--   IsLess→isLess {x} (cons {x' = x'} x<x' x<xs) with x ≤'? x'
--   IsLess→isLess {x} (cons {_} {.x} x<x' x<xs) | yes ≤′-refl = contr x<x'
--     where
--       contr : ∀ {x} -> suc x ≤ x -> ⊥
--       contr {zero} ()
--       contr {suc x} (s≤s sx≤x) = contr sx≤x
--   IsLess→isLess {x} (cons {_} {.(suc _)} x<x' x<xs) | yes (≤′-step p) = ⊤.tt
--   IsLess→isLess {x} (cons {_} {x'} x<x' x<xs) | no ¬x≤′x' = ¬x≤′x' (≤⇒≤′ (sucx≤y→x≤y x<x'))
--     where
--       sucx≤y→x≤y : ∀ {x y} -> suc x ≤ y -> x ≤ y
--       sucx≤y→x≤y {zero} sx≤y = z≤n
--       sucx≤y→x≤y {suc x} (s≤s sx≤y) = s≤s (sucx≤y→x≤y sx≤y)
--
-- open import Data.Sum
--
--
-- isLess→IsLess : ∀ {x xs} -> isLess x xs -> IsLess x xs
-- isLess→IsLess {x} {[]O} ⊤.tt = nil
-- isLess→IsLess {x} {x' ∷O xs} x< with x ≤'? x'
-- isLess→IsLess {.x'} {x' ∷O xs} () | yes ≤′-refl
-- isLess→IsLess {x} {(.(suc _) ∷O xs) {sn<}} ⊤.tt | yes (≤′-step {n = n} x≤′n) = {!sn<   !}
--   where
--     aux : x < suc n
--     aux = {! sn<  !}
--
--     rec : IsLess (suc n) xs
--     rec = isLess→IsLess sn<
--   --
--     aux₂ : IsLess x ((suc n ∷O xs) {sn<})
--     aux₂ = cons aux rec
--
-- isLess→IsLess {x} {x' ∷O xs} x< | no ¬p = {!   !}


mutual
  data OList : Set where
    []O : OList
    _∷O_ : (x : ℕ) -> (xs : OList) -> {x< : IsLess x xs} -> OList

  data IsLess : ℕ -> OList -> Set where
    base : ∀ {x} -> IsLess x []O
    step : ∀ {x x' xs} -> x < x' -> (x'<xs : IsLess x' xs) -> IsLess x ((x' ∷O xs) {x'<xs})





IsLess→< : ∀ {x x' xs x'<} -> IsLess x ((x' ∷O xs) {x'<}) -> x < x'
IsLess→< (step x<x' _) = x<x'

mutual
  insertO : ℕ -> OList -> OList
  insertO x []O = (x ∷O []O) {base}
  insertO x (x' ∷O xs) with x ≤'? x'
  insertO x ((.x ∷O xs) {x<}) | yes ≤′-refl = (x ∷O xs) {x<}
  insertO x ((.(suc _) ∷O xs) {x<}) | yes (≤′-step {n = x'} p) = (x ∷O (((suc x') ∷O xs) {x<})) {step (s≤s (≤′⇒≤ p)) x<}
  insertO x ((x' ∷O xs) {x'<}) | no x'<x = (x' ∷O insertO x xs) {insertO-lemma xs x'< x'<x}

  insertO-lemma : ∀ {x x'} xs -> IsLess x' xs -> ¬ x ≤′ x' -> IsLess x' (insertO x xs)
  insertO-lemma []O base ¬x≤′x' = step (≰⇒> (λ x≤x' → ¬x≤′x' (≤⇒≤′ x≤x'))) base
  insertO-lemma {x} {x'} (x'' ∷O xs) x'<xs x'<x with x ≤'? x''
  insertO-lemma {.x''} {x'} ((x'' ∷O xs) {x''<}) x'<xs _ | yes ≤′-refl = step (IsLess→< x'<xs) x''<
  insertO-lemma {x} {x'} ((.(suc _) ∷O xs) {sn<xs}) x'<xs ¬x≤′x' | yes (≤′-step x≤′n) =
    step (≰⇒> (λ x≤x' → ¬x≤′x' (≤⇒≤′ x≤x'))) (step (s≤s (≤′⇒≤ x≤′n)) sn<xs)
  insertO-lemma {x} {x'} ((x'' ∷O xs) {x''<xs}) x'<xs _ | no x''<x = step (IsLess→< x'<xs) (insertO-lemma {x} {x''} xs x''<xs x''<x)

data _∈O_ : ℕ -> OList -> Set where
  here : ∀ {x xs x<xs} -> x ∈O ((x ∷O xs) {x<xs})
  there : ∀ {x y xs y<xs} -> x ∈O xs -> x ∈O ((y ∷O xs) {y<xs})

_∉O_ : ℕ -> OList -> Set
x ∉O xs = ¬ (x ∈O xs)


IsLess-remove : ∀ {x x'} xs {x'<xs} -> IsLess x ((x' ∷O xs) {x'<xs}) -> IsLess x xs
IsLess-remove []O x<x∷xs = base
IsLess-remove ((x'' ∷O xs) {x''<xs}) (step x<x' x'<x''∷xs) = step (<-trans x<x' (IsLess→< x'<x''∷xs)) x''<xs

mutual
  removeO : ℕ -> OList -> OList
  removeO x []O = []O
  removeO x (x' ∷O xs) with x ≟ x'
  removeO x (.x ∷O xs) | yes refl = xs
  removeO x ((x' ∷O xs) {x'<xs}) | no ¬p = (x' ∷O removeO x xs) {removeO-lemma {x} {x'} xs x'<xs}

  removeO-lemma : ∀ {x x'} xs -> IsLess x' xs -> IsLess x' (removeO x xs)
  removeO-lemma []O x'<xs = base
  removeO-lemma {x} {x'} (x'' ∷O xs) x'<xs with x ≟ x''
  removeO-lemma {.x''} {x'} (x'' ∷O xs) x<xs | yes refl = IsLess-remove xs x<xs
  removeO-lemma {x} {x'} ((x'' ∷O xs) {x''<xs}) x'<xs | no ¬p = step (IsLess→< x'<xs) (removeO-lemma {x} {x''} xs x''<xs)



-- isLess : ℕ -> OList -> Set
-- isLess x []O = ⊤
-- isLess x (y ∷O ol) with x ≤'? y
-- isLess x (.x ∷O ol) | yes ≤′-refl = ⊥
-- isLess x (.(suc _) ∷O ol) | yes (≤′-step _) = ⊤
-- isLess x (y ∷O ol) | no _ = ⊥
--


-- smart constructor for OList
_∷O'_ : (x : ℕ) -> (xs : OList) -> OList
x ∷O' xs = insertO x xs

testOList : OList
testOList = 2 ∷O' (1 ∷O' (2 ∷O' []O))



data Formula' : OList → Set where
  -- _⟨_⟩ : Name → ∀ {xs} (ts : TTermList xs) → Formula xs
  _∧_ : ∀ {ns} → Formula' ns → Formula' ns → Formula' ns
  _∨_ : ∀ {ns} → Formula' ns → Formula' ns → Formula' ns
  _⟶_ : ∀ {ns} → Formula' ns → Formula' ns → Formula' ns
  ∘ : ∀ {ns} v → Formula' ns → {v∉ : v ∉O ns} → Formula' (insertO v ns)
  -- [_/_] : ∀ {y ns} → Term → (x : ℕ) → {x∈ : x ∈ ns} → {y⊆ : y ⊆ ns} → {x≠y : [ x ] ≢ y} → Formula ns → Formula (remove x ns)
  -- [_//_] : ∀ {y ns} → Term y → (x : ℕ) → {x⊆ : x ∈ ns} → {y⊈ : y ⊈ ns} → {x≠y : [ x ] ≢ y} → Formula ns → Formula (union y (remove x ns))
  All : ∀ {ns} v → Formula' ns → Formula' (removeO v ns)
  Ex : ∀ {ns} v → Formula' ns → Formula' (removeO v ns)




-- insert-reomve-id : ∀ {x n m} -> n ≡ m -> n ≡ insertO x (removeO x m)
-- insert-reomve-id {x} {xs} refl = {! xs  !}


rem-inj : ∀ {n m} x -> n ≡ m -> remove x n ≡ remove x m
rem-inj _ refl = refl

data _⊢⟨_⟩_ : ∀ {n m} → Structure n → n ≡ m -> Structure m → Set where
  atom : ∀ {n xs n≡m} {ts us : TTermList xs} →
    ∣ n ⟨ ts ⟩ ∣ ⊢⟨ n≡m ⟩ ∣ n ⟨ us ⟩ ∣
  allR : ∀ {x n m n≡m X} {Y : Structure m} →
    Y ⊢⟨ n≡m ⟩ Q {n} x ∣ X ∣ →
    -------------------
    Y ⊢⟨ n≡m ⟩ ∣ All {n} x X ∣
  allL : ∀ {x n m n≡m X} {Y : Formula m} →
            ∣ X ∣ ⊢⟨ n≡m ⟩ ∣ Y ∣ →
    -------------------------------
    ∣ All {n} x X ∣ ⊢⟨ rem-inj x n≡m ⟩ Q {m} x ∣ Y ∣
  IL : ∀ {n m n≡m} {X : Structure n} {Y : Structure m} →
       X ⊢⟨ n≡m ⟩ Y →
    -------------------
    (I , X) {refl} ⊢⟨ n≡m ⟩ Y
  IL2 : ∀ {n m n≡m} {X : Structure n} {Y : Structure m} →
    (I , X) {refl} ⊢⟨ n≡m ⟩ Y →
    -------------------
       X ⊢⟨ n≡m ⟩ Y
  IR : ∀ {n m n≡m} {X : Structure n} {Y : Structure m} →
      X ⊢⟨ n≡m ⟩ Y →
   -----------------
   X ⊢⟨ n≡m ⟩ (Y , I) {refl}
  IR2 : ∀ {n m n≡m} {X : Structure n} {Y : Structure m} →
    X ⊢⟨ n≡m ⟩ (Y , I) {refl} →
    -----------------
    X ⊢⟨ n≡m ⟩ Y

  ,>>disp : ∀ {n m n≡m} {Z : Structure n} {X Y : Structure m} →
    Z ⊢⟨ n≡m ⟩ (X , Y) {refl} →
    -----------------
    (X >> Z) {sym n≡m} ⊢⟨ refl ⟩ Y
  ,>>disp2 : ∀ {n m n≡m} {Z : Structure n} {X Y : Structure m} →
    (X >> Z) {sym n≡m} ⊢⟨ refl ⟩ Y →
    -----------------
    Z ⊢⟨ n≡m ⟩ (X , Y) {refl}
  ○IR : ∀ {x n m n≡m x∉m} {X : Structure n} →
    X ⊢⟨ n≡m ⟩ (I {insert x m}) →
    -----------------
    X ⊢⟨ n≡m ⟩ ○ x (I {m}) {x∉m}
  ○IR2 : ∀ {x n m n≡m x∉m} {X : Structure n} →
    X ⊢⟨ n≡m ⟩ ○ x (I {m}) {x∉m}  →
    -----------------
    X ⊢⟨ n≡m ⟩ (I {insert x m})
  -- ,<<disp : ∀ {n m n≡m} {X : Structure n} {Y Z : Structure m} →
  --   X ⊢⟨ n≡m ⟩ (Y , Z) {refl} →
  --   -----------------
  --   (X >> Z) {n≡m} ⊢⟨ n≡m ⟩ Y
  -- ,<<disp2 : ∀ {n m n≡m} {X : Structure n} {Y Z : Structure m} →
  --   (X >> Z) {n≡m} ⊢⟨ n≡m ⟩ Y →
  --   -----------------
  --   X ⊢⟨ n≡m ⟩ (Y , Z) {refl}
rem-union-id : ∀ x -> remove x (union [ x ] []) ≡ []
rem-union-id x rewrite remove-rewrite x {[]} = refl




test : ∀ x y {n} -> ∣ All x (n ⟨ (TVar x) ∷T []T ⟩) ∣ ⊢⟨ PropEq.trans (rem-union-id x) (sym (rem-union-id y)) ⟩ ∣ All y (n ⟨ (TVar y) ∷T []T ⟩) ∣
test x y = allR ?


data Map : List ℕ → Set where
  nil : Map []
  _/_:::_ : ∀ {xs} (x : ℕ) → String → Map xs → Map (x ∷ xs)


_!!_ : List (ℕ × String) → ℕ → String
[] !! _ = "not found"
((x , s) ∷ m) !! y with x ≟ y
... | yes _ = s
... | no _ = m !! y



Term→Str : List (ℕ × String) → Term → String
Term→Str m (Var x) = "\\textit{" ++ (m !! x) ++ "}"
Term→Str m (Const s) = "\\textbf{" ++ s ++ "}"
Term→Str m (Fun n args) = "" --"\\textbf{" ++ s ++ "}"
-- Term→Str m ([[_/_]]_ _ _ _) = "" --"\\textbf{" ++ s ++ "}"
Term→Str m ([[[_]]]_ _ _) = ""


Formula→Str : ∀ {xs} → List (ℕ × String) → Formula xs → String
Formula→Str m (n ⟨ args ⟩) = n ++ "(" ++ ")" --aux args ++ ")"
  -- where
  -- aux : List Term → String
  -- aux [] = ""
  -- aux (x ∷ []) = Term→Str m x
  -- aux (x ∷ (y ∷ args)) = Term→Str m x ++ ", " ++ aux (y ∷ args)
Formula→Str m (f ∧ f₁) = Formula→Str m f ++ " \\land " ++ Formula→Str m f₁
Formula→Str m (f ∨ f₁) = Formula→Str m f ++ " \\lor " ++ Formula→Str m f₁
Formula→Str m (f ⟶ f₁) = Formula→Str m f ++ " \\leftarrow " ++ Formula→Str m f₁
Formula→Str m (∘ v f) = "\\circ_" ++ (m !! v) ++ Formula→Str m f
-- Formula→Str m ([ y / x ] f) = "(" ++ Term→Str m y ++ "/" ++ (m !! x) ++ ") " ++ Formula→Str m f
-- Formula→Str m ([ y // x ] f) = "(" ++ Term→Str m y ++ "//" ++ (m !! x) ++ ") " ++ Formula→Str m f
Formula→Str m (All v f) = "\\forall " ++ (m !! v) ++ Formula→Str m f
Formula→Str m (Ex v f) = "\\exists " ++ (m !! v) ++ Formula→Str m f

Structure→Str : ∀ {xs} → List (ℕ × String) → Structure xs → String
Structure→Str m ∣ x ∣ = Formula→Str m x
Structure→Str m (s , s₁) = Structure→Str m s ++ " , " ++ Structure→Str m s₁
Structure→Str m (s >> s₁) = Structure→Str m s ++ " >> " ++ Structure→Str m s₁
Structure→Str m (s << s₁) = Structure→Str m s ++ " << " ++ Structure→Str m s₁
Structure→Str m I = "I"
Structure→Str m (○ v s) = "\\bigcirc_" ++ (m !! v) ++ Structure→Str m s
Structure→Str m (Q v s) = "Q " ++ (m !! v) ++ Structure→Str m s


⊢concl : ∀ {n} {xs ys : Structure n} → xs ⊢ ys → (Structure n × Structure n)
⊢concl {_} {xs} {ys} _ = xs , ys

data ⊢List : Set where
  ⊢nil : ⊢List
  _⊢::_ : ∀ {n} {xs ys : Structure n} → xs ⊢ ys → ⊢List → ⊢List

⊢prems : ∀ {n} {xs ys : Structure n} → xs ⊢ ys → ⊢List
⊢prems atom = ⊢nil
⊢prems (allR xs⊢ys) = xs⊢ys ⊢:: ⊢nil
⊢prems (allL xs⊢ys) = xs⊢ys ⊢:: ⊢nil


-- proof1 : ∀ {n} P (args : TList n) → ∣ P ⟨ args ⟩ ∣ ⊢ ∣ P ⟨ args ⟩ ∣
-- proof1 P args = atom
--
-- proof : ∣ "P" ⟨ Var 0 ::: nil ⟩ ∣ ⊢ ∣ "P" ⟨ Var 0 ::: nil ⟩ ∣
-- proof = let (x , y) = ⊢concl (proof1 "P"  (Var 0 ::: nil)) in {!Structure→Str [ (0 , "x") ] x  !}

⊢→Str' : ∀ {n} {xs ys : Structure n} → List (ℕ × String) → xs ⊢ ys → String
⊢→Str' m xs⊢ys with ⊢concl xs⊢ys | ⊢prems xs⊢ys
⊢→Str' m xs⊢ys | xs , ys | prems = Structure→Str m xs ++ " \\vdash " ++ Structure→Str m ys
  where
    prems→Str : ⊢List → String
    prems→Str ⊢nil = ""
    prems→Str (x ⊢:: lst) = {!   !}




open import IO

main = run (putStrLn "Hello, world!")
