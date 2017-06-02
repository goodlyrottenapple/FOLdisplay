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


-- data Img {A B : Set} (f : A → B) (y : B) : Set₁ where
--   intro : ∃ (λ x → f x ≡ y) → Img f y
--
-- const : ℕ → ℕ
-- const _ = 1
--
-- lemma : Img const 1
-- lemma = intro (0 , refl)
--
--
-- lemma₁ : ¬ (Img const 2)
-- lemma₁ (intro (x , ()))
--
--
-- import Data.Nat.Properties as ℕ
-- open import Relation.Binary using (module StrictTotalOrder)
--
-- open import Data.AVL.Sets (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)

-- import Data.AVL as AVL
-- open import Funionction
-- open import Data.unionit

-- _∪'_ : ∀ {n m} → Subset n → Subset m → Subset (n ⊔ m)
-- [] ∪' [] = []
-- [] ∪' (x ∷ m) = (x ∷ m)
-- (x ∷ xs) ∪' [] = (x ∷ xs)
-- (x ∷ xs) ∪' (y ∷ ys) = (x ∨B y) ∷ (xs ∪' ys)
--
-- extend : ∀ {n} → Subset n → Subset (suc n)
-- extend [] = [ Data.Bool.true ]
-- extend (x ∷ xs) = x ∷ (extend xs)

--
-- _∪S_ : ⟨Set⟩ → ⟨Set⟩ → ⟨Set⟩
-- a ∪S b = AVL.unionion (const Data.unionit.⊤) (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder) a b
--
--
-- unionions : List ⟨Set⟩ → ⟨Set⟩
-- unionions xs = AVL.unionions (const Data.unionit.⊤) (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder) xs
--

Name : Set
Name = String


insert : ℕ -> List ℕ -> List ℕ
insert n List.[] = n ∷ []
insert n (x ∷ l) with n ≟ x
insert n (.n ∷ l) | yes refl = n ∷ l
insert n (x ∷ l) | no n≠x with n ≤? x
insert n (x ∷ l) | no n≠x | yes n<x = n ∷ x ∷ l
insert n (x ∷ l) | no n≠x | no n>x = x ∷ insert n l


-- data FSet : List ℕ -> Set where
--   ⊘ : FSet List.[]
--   -- single : ∀ n -> FSet (n List.∷ List.[])
--   _:::_ : ∀ n {ns} -> FSet ns -> FSet (insert n ns)
--

sortRemDups : List ℕ -> List ℕ
sortRemDups [] = []
sortRemDups (x ∷ xs) = insert x (sortRemDups xs)

-- singleton' : (n : ℕ) -> FSet [ n ]
-- singleton' n = n ::: ⊘


-- fromList' : (ns : List ℕ) -> FSet (sortRemDups ns)
-- fromList' [] = ⊘
-- fromList' (x ∷ xs) = x ::: fromList' xs
--

-- union : List ℕ -> List ℕ -> List ℕ
-- union [] ys = ys
-- union xs [] = xs
-- union (x ∷ xs) (y ∷ ys) with x Data.Nat.≤? y
-- union (x ∷ xs) (y ∷ ys) | yes x≤y with x Data.Nat.≟ y
-- union (x ∷ xs) (y ∷ ys) | yes x≤y | yes x≡y = x ∷ union xs ys
-- union (x ∷ xs) (y ∷ ys) | yes x≤y | no x<y = x ∷ union xs (y ∷ ys)
-- union (x ∷ xs) (y ∷ ys) | no x>y = y ∷ union (x ∷ xs) ys


union : List ℕ -> List ℕ -> List ℕ
union [] ys = ys
union (x ∷ xs) ys = insert x (union xs ys)


-- union-insert≡ : ∀ x xs ys -> union (insert x xs) ys ≡ insert x (union xs ys)
-- union-insert≡ x [] ys = refl
-- union-insert≡ x (x' ∷ xs) ys with x Data.Nat.≤? x'
-- union-insert≡ x (x' ∷ xs) ys | yes x≤x' with x Data.Nat.≟ x'
-- union-insert≡ x (x' ∷ xs) ys | yes x≤x' | yes x≡x' = {!   !}
-- union-insert≡ x (x' ∷ xs) ys | yes x≤x' | no x<x' = {!   !}
-- union-insert≡ x (x' ∷ xs) ys | no x>x' = {!   !}


-- unionion' : ∀ {n m} -> FSet n -> FSet m -> FSet (union n m)
-- unionion' ⊘ ys = ys
-- unionion' {_} {ms} (_:::_ x {ns} xs) ys rewrite union-insert≡ x ns ms = x ::: unionion' xs ys

remove : ℕ -> List ℕ -> List ℕ
remove n [] = []
remove n (x ∷ xs) with n Data.Nat.≟ x
remove n (x ∷ xs) | yes p = xs
remove n (x ∷ xs) | no ¬p = x ∷ remove n xs


-- xs \\ ys
diff : List ℕ -> List ℕ -> List ℕ
diff xs [] = xs
diff xs (x ∷ ys) = diff (remove x xs) ys

mutual
  data Term : Set where
    Var : ℕ → Term
    Const : Name -> Term
    Fun : Name -> List Term → Term
    -- [[_/_]]_ : Term -> ℕ -> Term -> Term
    [[[_]]]_ : List (Term × ℕ) -> Term -> Term

  -- data TList : Set where
  --   nil : TList
  --   _:::_ : -> Term x -> TList xs -> TList (union x xs)


-- length : ∀ {a} -> TList a -> ℕ
-- length nil = 0
-- length (_ ::: tlist) = suc (length tlist)


-- mapSubst : Term -> ℕ -> Lis a -> TList []
-- mapSubst y x nil = nil
-- mapSubst y x (t ::: tlist) = ([[ y / x ]] t) ::: (mapSubst y x tlist)

mutual
  data _⊢≡_ : Term -> Term -> Set where
    atom : ∀ {n} -> Var n ⊢≡ Var n
    atomC : ∀ {n} -> Const n ⊢≡ Const n
    funEq : ∀ {n arg1 arg2} -> arg1 ≡ₗ arg2 -> Fun n arg1 ⊢≡ Fun n arg2
    -- subMon : ∀ {substs X Y} -> X ⊢≡ Y -> ([[[ substs ]]] X) ⊢≡ ([[[ substs ]]] Y) -- this rule is derivable
    sub[]R : ∀ {X Y} -> X ⊢≡ Y -> X ⊢≡ ([[[ [] ]]] Y)
    sub[]L : ∀ {X Y} -> X ⊢≡ Y -> ([[[ [] ]]] X) ⊢≡ Y
    subAtomEqR : ∀ {x t lst X} -> X ⊢≡ ([[[ lst ]]] t) -> X ⊢≡ ([[[ (t , x) ∷ lst ]]] (Var x))
    subAtomEqL : ∀ {x t lst Y} -> ([[[ lst ]]] t) ⊢≡ Y -> ([[[ (t , x) ∷ lst ]]] (Var x)) ⊢≡ Y

    subAtomNeqR : ∀ {x y t lst X} -> X ⊢≡ ([[[ lst ]]] (Var x)) -> x ≢ y -> X ⊢≡ ([[[ (t , y) ∷ lst ]]] (Var x))
    subAtomNeqL : ∀ {x y t lst Y} -> ([[[ lst ]]] (Var x)) ⊢≡ Y -> x ≢ y -> ([[[ (t , y) ∷ lst ]]] (Var x)) ⊢≡ Y

    subAtomCR : ∀ {n lst X} -> X ⊢≡ (Const n) -> X ⊢≡ ([[[ lst ]]] (Const n))
    subAtomCL : ∀ {n lst Y} -> (Const n) ⊢≡ Y -> ([[[ lst ]]] (Const n)) ⊢≡ Y

    subFunR : ∀ {n arg lst X} -> X ⊢≡ (Fun n (List.map ([[[_]]]_ lst) arg)) -> X ⊢≡ ([[[ lst ]]] (Fun n arg))
    subFunL : ∀ {n arg lst Y} -> (Fun n (List.map ([[[_]]]_ lst) arg)) ⊢≡ Y -> ([[[ lst ]]] (Fun n arg)) ⊢≡ Y

    subConsR : ∀ {lst lst' X Y} -> X ⊢≡ ([[[ lst List.++ lst' ]]] Y) -> X ⊢≡ ([[[ lst' ]]] ([[[ lst ]]] Y))
    subConsL : ∀ {lst lst' X Y} -> ([[[ lst List.++ lst' ]]] X) ⊢≡ Y -> ([[[ lst' ]]] ([[[ lst ]]] X)) ⊢≡ Y

    -- dispL : ∀ {x y X Y} -> ([[ y / x ]] X) ⊢≡ Y -> X ⊢≡ ([[ y / x ]]⁻ Y)
    -- dispL2 : ∀ {x y X Y} -> X ⊢≡ ([[ y / x ]]⁻ Y) -> ([[ y / x ]] X) ⊢≡ Y
    -- dispR : ∀ {x y X Y} -> X ⊢≡ ([[ y / x ]] Y) -> ([[ y / x ]]⁻ X) ⊢≡ Y
    -- dispR2 : ∀ {x y X Y} -> ([[ y / x ]]⁻ X) ⊢≡ Y -> X ⊢≡ ([[ y / x ]] Y)


  data _≡ₗ_ : List Term -> List Term -> Set where
    []≡ : [] ≡ₗ []
    _∷≡_ : {xs : List Term} {ys : List Term} {t1 t2 : Term} -> t1 ⊢≡ t2 -> xs ≡ₗ ys -> (t1 ∷ xs) ≡ₗ (t2 ∷ ys)




open import Data.Maybe using (Maybe; just; nothing; monad)

open import Category.Monad using (RawMonad)
open import Agda.Primitive as P

open RawMonad (monad {P.lzero}) using (_>>=_;return)
-- open Category.Monad.rawMonad
open import Data.String using () renaming (_≟_ to _≟S_)



-- inv-subFunL : ∀ {nm x t args args₁} -> Fun nm args ⊢≡ ([[ t / x ]] Fun nm args₁) -> args ≡ₗ List.map ([[_/_]]_ t x) args₁
-- inv-subFunL (subFunR (funEq x₁)) = x₁
-- -- inv-subFunL (dispR2 (dispR ⊢≡)) = inv-subFunL ⊢≡



data Term' : Set where
  Var' : ℕ → Term'
  Const' : Name -> Term'
  Fun' : Name -> List Term' → Term'


mutual
  sub : ℕ -> Term' -> Term' -> Term'
  sub x t' (Var' x') with x ≟ x'
  ... | yes _ = t'
  ... | no _ = (Var' x')
  sub x t' (Const' n) = Const' n
  sub x t' (Fun' n args) = Fun' n (subList x t' args)

  subList : ℕ -> Term' -> List Term' -> List Term'
  subList x t' [] = []
  subList x t' (t ∷ l) = sub x t' t ∷ subList x t' l


mutual
  Term→Term' : Term -> Term'
  Term→Term' (Var x) = Var' x
  Term→Term' (Const c) = Const' c
  Term→Term' (Fun n args) = Fun' n (LTerm→LTerm' args)
  Term→Term' ([[[ lst ]]] t) = STerm lst (Term→Term' t)

  LTerm→LTerm' : List Term -> List Term'
  LTerm→LTerm' [] = []
  LTerm→LTerm' (x ∷ l) = Term→Term' x ∷ LTerm→LTerm' l

  STerm : List (Term × ℕ) -> Term' -> Term'
  STerm [] t = t
  STerm ((t' , x) ∷ lst) t = STerm lst (sub x (Term→Term' t') t)






mutual
  ⊢≡symm : ∀ {t1 t2 : Term} -> t1 ⊢≡ t2 -> t2 ⊢≡ t1
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

  ≡ₗsymm : ∀ {arg1 arg2} -> arg1 ≡ₗ arg2 -> arg2 ≡ₗ arg1
  ≡ₗsymm []≡ = []≡
  ≡ₗsymm (x ∷≡ arg1≡ₗarg2) = (⊢≡symm x) ∷≡ (≡ₗsymm arg1≡ₗarg2)



≡-Fun-nm : ∀ {n n' args args'} -> Fun' n args ≡ Fun' n' args' -> n ≡ n'
≡-Fun-nm refl = refl

≡-Fun-args : ∀ {n args args'} -> Fun' n args ≡ Fun' n args' -> args ≡ args'
≡-Fun-args refl = refl

Fun-args-≡ : ∀ {n args args'} -> args ≡ args' -> Fun' n args ≡ Fun' n args'
Fun-args-≡ refl = refl




substFun≡aux : ∀ {n} lst args -> STerm lst (Fun' n args) ≡ Fun' n (List.map (STerm lst) args)
substFun≡aux [] args = Fun-args-≡ (aux args)
  where
    aux : ∀ args -> args ≡ List.map (STerm []) args
    aux [] = refl
    aux (a ∷ args) = cong (_∷_ a) (aux args)
substFun≡aux {n} ((t , x) ∷ lst) args = PropEq.trans (substFun≡aux {n} lst (subList x (Term→Term' t) args)) (Fun-args-≡ (aux lst x t args))
  where
    aux : ∀ lst x t args -> List.map (STerm lst) (subList x (Term→Term' t) args) ≡ List.map (STerm ((t , x) ∷ lst)) args
    aux lst x t [] = refl
    aux lst x t (x' ∷ args) = cong (_∷_ (STerm lst (sub x (Term→Term' t) x'))) (aux lst x t args)

substFun≡ : ∀ {n} args lst -> Term→Term' ([[[ lst ]]] Fun n args) ≡ Fun' n (LTerm→LTerm' (List.map ([[[_]]]_ lst) args))
substFun≡ [] [] = refl
substFun≡ [] (s ∷ lst) = substFun≡ [] lst
substFun≡ (a ∷ args) [] = Fun-args-≡ (cong (_∷_ (Term→Term' a)) (LTerm[]Subst args))
  where
    LTerm[]Subst : ∀ args -> LTerm→LTerm' args ≡ LTerm→LTerm' (List.map ([[[_]]]_ []) args)
    LTerm[]Subst [] = refl
    LTerm[]Subst (a ∷ args) = cong (_∷_ (Term→Term' a)) (LTerm[]Subst args)
substFun≡ (a ∷ args) ((t , x) ∷ lst) = PropEq.trans
  (substFun≡aux lst (subList x (Term→Term' t) (LTerm→LTerm' (a ∷ args))))
  (Fun-args-≡ (aux (a ∷ args)))
  where
    aux : ∀ args {lst x t} -> List.map (STerm lst) (subList x (Term→Term' t) (LTerm→LTerm' args)) ≡ LTerm→LTerm' (List.map ([[[_]]]_ ((t , x) ∷ lst)) args)
    aux [] = refl
    aux (a ∷ args) {lst} {x} {t} = cong (_∷_ (STerm lst (sub x (Term→Term' t) (Term→Term' a)))) (aux args)


++[]-id : ∀ {a} {A : Set a} (lst : List A) -> lst List.++ [] ≡ lst
++[]-id [] = refl
++[]-id (x ∷ xs) = cong (_∷_ x) (++[]-id xs)


substSubst≡ : ∀ {lst lst' t} -> Term→Term' ([[[ lst ]]] ([[[ lst' ]]] t)) ≡ Term→Term' ([[[ lst' List.++ lst ]]] t)
substSubst≡ {[]} {lst'} rewrite ++[]-id lst' = refl
substSubst≡ {(t , x₂) ∷ lst} {[]} = refl
substSubst≡ {(t , x) ∷ lst} {(t' , x') ∷ lst'} {t''} = substSubst≡ {(t , x) ∷ lst} {lst'} {[[[ [ (t' , x') ]  ]]] t''}

subsConst≡ : ∀ {lst c} -> Term→Term' ([[[ lst ]]] (Const c)) ≡ Const' c
subsConst≡ {[]} = refl
subsConst≡ {_ ∷ lst} {c} = subsConst≡ {lst} {c}


open import Data.List.Properties

substTac : (t1 : Term) -> (t2 : Term) -> {_ : Term→Term' t1 ≡ Term→Term' t2} -> t1 ⊢≡ t2
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
    eq' : ∀ {x t t' lst} -> t ≡ Term→Term' (([[[ (t' , x) ∷ lst ]]] Var x)) -> t ≡ Term→Term' ([[[ lst ]]] t')
    eq' {x} refl with x ≟ x
    eq' {x} refl | yes _ = refl
    eq' {x} refl | no ¬p = ⊥-elim (¬p refl)
substTac t1 ([[[ (t , x') ∷ lst ]]] Var x) {eq} | no ¬p = subAtomNeqR (substTac t1 ([[[ lst ]]] (Var x)) {eq' {x} {x'} {Term→Term' t1} {t} {lst} eq ¬p}) ¬p
  where
    eq' : ∀ {x x' t t' lst} -> t ≡ Term→Term' (([[[ (t' , x') ∷ lst ]]] Var x)) -> x ≢ x' -> t ≡ Term→Term' ([[[ lst ]]] Var x)
    eq' {x} {x'} refl x≠x' with x' ≟ x
    eq' {x} {.x} refl x≠x' | yes refl = ⊥-elim (x≠x' refl)
    eq' {x} {x'} refl x≠x' | no ¬p = refl
substTac t1 ([[[ x ∷ lst ]]] Const c) {eq} = subAtomCR (substTac t1 (Const c) {PropEq.trans eq (subsConst≡ {x ∷ lst} {c})})
substTac t1 ([[[ x ∷ lst ]]] Fun n args) {eq} = subFunR (substTac t1 (Fun n (List.map ([[[_]]]_ (x ∷ lst)) args)) {PropEq.trans eq (substFun≡ args (x ∷ lst))})

substTac t1 ([[[ x ∷ lst ]]] ([[[ lst' ]]] t2)) {eq} =
  subConsR (substTac t1 ([[[ lst' List.++ x ∷ lst ]]] t2) {PropEq.trans eq (substSubst≡ {x ∷ lst} {lst'} {t2})})

substTac ([[[ lst ]]] t1) t2 {eq} = ⊢≡symm (substTac t2 ([[[ lst ]]] t1) {sym eq}) -- adga doesn't like this, but it should be fine...



⊢≡-≡ : ∀ {X Y} -> X ⊢≡ Y -> Term→Term' X ≡ Term→Term' Y
⊢≡-≡ atom = refl
⊢≡-≡ atomC = refl
⊢≡-≡ (funEq x) = Fun-args-≡ (≡ₗ→≡ x)
  where
    ∷-≡ : ∀ {a} {A : Set a} {x y : A} {xs ys} -> x ≡ y -> xs ≡ ys -> x ∷ xs ≡ y ∷ ys
    ∷-≡ refl refl = refl

    ≡ₗ→≡ : ∀ {arg1 arg2} -> arg1 ≡ₗ arg2 -> (LTerm→LTerm' arg1) ≡ (LTerm→LTerm' arg2)
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
  ⊢≡atom : ∀ {t} -> t ⊢≡ t
  ⊢≡atom {Var x} = atom
  ⊢≡atom {Const x} = atomC
  ⊢≡atom {Fun x x₁} = funEq ≡ₗatom
    where
      ≡ₗatom : ∀ {xs} -> xs ≡ₗ xs
      ≡ₗatom {[]} = []≡
      ≡ₗatom {x ∷ xs} = ⊢≡atom ∷≡ ≡ₗatom
  ⊢≡atom {[[[ x ]]] t} = ⊢≡subMon ⊢≡atom


  ⊢≡subMon : ∀ {sub X Y} -> X ⊢≡ Y -> ([[[ sub ]]] X) ⊢≡ ([[[ sub ]]] Y)
  ⊢≡subMon {sub} {X} {Y} X⊢≡Y = substTac ([[[ sub ]]] X) ([[[ sub ]]] Y) {mon {sub} {Term→Term' X} {Term→Term' Y} (⊢≡-≡ X⊢≡Y)}
    where
      mon : ∀ {sub X Y} -> X ≡ Y -> STerm sub X ≡ STerm sub Y
      mon refl = refl


data _∈_ : ℕ -> List ℕ -> Set where
  here : ∀ {x xs} -> x ∈ (x ∷ xs)
  there : ∀ {x y xs} -> x ∈ xs -> x ∈ (y ∷ xs)

data _⊆_ : List ℕ -> List ℕ -> Set where
  nil : ∀ {xs} -> [] ⊆ xs
  cons : ∀ {x xs ys} -> x ∈ ys -> xs ⊆ ys -> (x ∷ xs) ⊆ ys

_∉_ : ℕ -> List ℕ -> Set
n ∉ ns = ¬ (n ∈ ns)

_⊈_ : List ℕ -> List ℕ -> Set
xs ⊈ ys = ¬ (xs ⊆ ys)

data Formula : List ℕ -> Set where
  -- _⟨_⟩ : ∀ {ns} → Name -> TList ns → Formula ns
  _∧_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  _∨_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  _⟶_ : ∀ {ns} → Formula ns → Formula ns → Formula ns
  ∘ : ∀ {ns} v → Formula ns → {v∉ : v ∉ ns} -> Formula (insert v ns)
  -- [_/_] : ∀ {y ns} -> Term -> (x : ℕ) -> {x∈ : x ∈ ns} -> {y⊆ : y ⊆ ns} -> {x≠y : [ x ] ≢ y} -> Formula ns -> Formula (remove x ns)
  -- [_//_] : ∀ {y ns} -> Term y -> (x : ℕ) -> {x⊆ : x ∈ ns} -> {y⊈ : y ⊈ ns} -> {x≠y : [ x ] ≢ y} -> Formula ns -> Formula (union y (remove x ns))
  All : ∀ {ns} v → Formula ns → Formula (remove v ns)
  Ex : ∀ {ns} v → Formula ns → Formula (remove v ns)


data Structure : List ℕ → Set where
  ∣_∣ : ∀ {n} → Formula n → Structure n
  _,_ : ∀ {n} → Structure n → Structure n → Structure n
  _>>_ : ∀ {n} → Structure n → Structure n → Structure n
  ○ : ∀ {n} v → Structure n → Structure (insert v n)
  Q : ∀ {n} v → Structure n → Structure (remove v n)



-- form : Formula (0 ∷ 2 ∷ [])
-- form = ("P" ⟨ (Var 2 ::: (Var 0 ::: (Var 2 ::: nil))) ⟩)
--
--
-- form1 : Formula (1 ∷ 2 ∷ [])
-- form1 = [ Var 1 / 0 ] {here} {cons (there here) nil} {λ ()} ("P" ⟨ (Var 0 ::: (Var 2 ::: (Var 1 ::: nil))) ⟩)
--
--
--
-- form2aux : [ 3 ] ⊈ (0 ∷ 1 ∷ 2 ∷ [])
-- form2aux (cons (there (there (there ()))) _)
--
--
-- form2 : Formula (1 ∷ 2 ∷ 3 ∷ [])
-- form2 = [ Var 3 // 0 ] {here} {form2aux} {λ ()} ("P" ⟨ (Var 0 ::: (Var 2 ::: (Var 1 ::: nil))) ⟩)

-- [ Var 0 / Var 0 ] ("P" ⟨ (Var 0 ::: (Var 2 ::: (Var 1 ::: nil))) ⟩)

data _⊢_ : ∀ {n} → Structure n → Structure n → Set where
  -- atom : ∀ {n} {ns} {xs : TList ns} →
  --   --------------------------
  --   ∣ n ⟨ xs ⟩ ∣ ⊢ ∣ n ⟨ xs ⟩ ∣
  allR : ∀ {x n X Y} →
    Y ⊢ Q {n} x ∣ X ∣ →
    -------------------
    Y ⊢ ∣ All {n} x X ∣
  allL : ∀ {x n X Y} →
            ∣ Y ∣ ⊢ ∣ X ∣ →
    -------------------------------
    ∣ All {n} x Y ∣ ⊢ Q {n} x ∣ X ∣


data Map : List ℕ -> Set where
  nil : Map []
  _/_:::_ : ∀ {xs} (x : ℕ) -> String -> Map xs -> Map (x ∷ xs)


--
-- lemma : ∀ x n -> ∣ All x (n ⟨ Var x ::: nil ⟩) ∣ ⊢ ∣ All x (n ⟨ Var x ::: nil ⟩) ∣
-- lemma x n = allR (allL atom)


_!!_ : List (ℕ × String) -> ℕ -> String
[] !! _ = "not found"
((x , s) ∷ m) !! y with x ≟ y
... | yes _ = s
... | no _ = m !! y



Term→Str : List (ℕ × String) -> Term -> String
Term→Str m (Var x) = "\\textit{" ++ (m !! x) ++ "}"
Term→Str m (Const s) = "\\textbf{" ++ s ++ "}"
Term→Str m (Fun n args) = "" --"\\textbf{" ++ s ++ "}"
-- Term→Str m ([[_/_]]_ _ _ _) = "" --"\\textbf{" ++ s ++ "}"
Term→Str m ([[[_]]]_ _ _) = ""

-- t→Str m (Fun nm args) = nm ++ "(" ++ aux args ++ ")"
--   where
--     aux : ∀ (xs : List ℕ) -> String
--     aux [] = ""
--     aux (x ∷ []) = (m !! x)
--     aux (x ∷ x₁ ∷ n) = (m !! x) ++ "," ++ aux (x₁ ∷ n)


-- mremove : ∀ {xs} -> (x : ℕ) -> Map xs -> Map (remove x xs)
-- mremove _ nil = nil
-- mremove x (y / s ::: m) with x ≟ y
-- ... | yes _ = m
-- ... | no _ = y / s ::: (mremove x m)
--
--
--
-- remove-insert-id : ∀ x xs -> x ∉ xs -> remove x (insert x xs) ≡ xs
-- remove-insert-id x [] _ with x ≟ x
-- ... | yes _ = refl
-- ... | no x≠x = ⊥-elim (x≠x refl)
-- remove-insert-id x (x' ∷ xs) _ with x ≟ x'
-- remove-insert-id x (.x ∷ xs) x∉xs | yes refl = ⊥-elim (x∉xs here)
-- remove-insert-id x (x' ∷ xs) _ | no _ with x ≤? x'
-- remove-insert-id x (x' ∷ xs) _ | no _ | yes _ with x ≟ x
-- remove-insert-id x (x' ∷ xs) _ | no _ | yes _ | yes refl = refl
-- remove-insert-id x (x' ∷ xs) _ | no _ | yes _ | no x≠x = ⊥-elim (x≠x refl)
-- remove-insert-id x (x' ∷ xs) _ | no p | no ¬p with x ≟ x'
-- remove-insert-id x (.x ∷ xs) _ | no x≠x' | no _ | yes refl = ⊥-elim (x≠x' refl)
-- remove-insert-id x (x' ∷ xs) x∉xs | no _ | no _ | no _ =
--   cong (_∷_ x') (remove-insert-id x xs (λ z → x∉xs (there z)))
--
--


Formula→Str : ∀ {xs} -> List (ℕ × String) -> Formula xs -> String
-- Formula→Str m (n ⟨ args ⟩) = n ++ "(" ++ aux args ++ ")"
--   where
--   aux : ∀ {xs} -> TList xs -> String
--   aux nil = ""
--   aux (x ::: nil) = Term→Str m x
--   aux (x ::: (y ::: args)) = Term→Str m x ++ ", " ++ aux (y ::: args)
Formula→Str m (f ∧ f₁) = Formula→Str m f ++ " \\land " ++ Formula→Str m f₁
Formula→Str m (f ∨ f₁) = Formula→Str m f ++ " \\lor " ++ Formula→Str m f₁
Formula→Str m (f ⟶ f₁) = Formula→Str m f ++ " \\leftarrow " ++ Formula→Str m f₁
Formula→Str m (∘ v f) = "\\circ_" ++ (m !! v) ++ Formula→Str m f
-- Formula→Str m ([ y / x ] f) = "(" ++ Term→Str m y ++ "/" ++ (m !! x) ++ ") " ++ Formula→Str m f
-- Formula→Str m ([ y // x ] f) = "(" ++ Term→Str m y ++ "//" ++ (m !! x) ++ ") " ++ Formula→Str m f
Formula→Str m (All v f) = "\\forall " ++ (m !! v) ++ Formula→Str m f
Formula→Str m (Ex v f) = "\\exists " ++ (m !! v) ++ Formula→Str m f

Structure→Str : ∀ {xs} -> List (ℕ × String) -> Structure xs -> String
Structure→Str m ∣ x ∣ = Formula→Str m x
Structure→Str m (s , s₁) = Structure→Str m s ++ " , " ++ Structure→Str m s₁
Structure→Str m (s >> s₁) = Structure→Str m s ++ " >> " ++ Structure→Str m s₁
Structure→Str m (○ v s) = "\\bigcirc_" ++ (m !! v) ++ Structure→Str m s
Structure→Str m (Q v s) = "Q " ++ (m !! v) ++ Structure→Str m s


⊢concl : ∀ {n} {xs ys : Structure n} -> xs ⊢ ys -> (Structure n × Structure n)
⊢concl {_} {xs} {ys} _ = xs , ys

data ⊢List : Set where
  ⊢nil : ⊢List
  _⊢::_ : ∀ {n} {xs ys : Structure n} -> xs ⊢ ys -> ⊢List -> ⊢List

⊢prems : ∀ {n} {xs ys : Structure n} -> xs ⊢ ys -> ⊢List
-- ⊢prems atom = ⊢nil
⊢prems (allR xs⊢ys) = xs⊢ys ⊢:: ⊢nil
⊢prems (allL xs⊢ys) = xs⊢ys ⊢:: ⊢nil


-- proof1 : ∀ {n} P (args : TList n) -> ∣ P ⟨ args ⟩ ∣ ⊢ ∣ P ⟨ args ⟩ ∣
-- proof1 P args = atom
--
-- proof : ∣ "P" ⟨ Var 0 ::: nil ⟩ ∣ ⊢ ∣ "P" ⟨ Var 0 ::: nil ⟩ ∣
-- proof = let (x , y) = ⊢concl (proof1 "P"  (Var 0 ::: nil)) in {!Structure→Str [ (0 , "x") ] x  !}

⊢→Str' : ∀ {n} {xs ys : Structure n} -> List (ℕ × String) -> xs ⊢ ys -> String
⊢→Str' m xs⊢ys with ⊢concl xs⊢ys | ⊢prems xs⊢ys
⊢→Str' m xs⊢ys | xs , ys | prems = Structure→Str m xs ++ " \\vdash " ++ Structure→Str m ys
  where
    prems→Str : ⊢List -> String
    prems→Str ⊢nil = ""
    prems→Str (x ⊢:: lst) = {!   !}



-- in Structure→Str m xs ++ " \\vdash " ++ Structure→Str m ys

--
-- ∈insert : ∀ x xs -> x ∈ insert x xs
-- ∈insert x [] = here
-- ∈insert x (x₁ ∷ xs) with x ≟ x₁
-- ∈insert x (.x ∷ xs) | yes refl = here
-- ∈insert x (x₁ ∷ xs) | no _ with x ≤? x₁
-- ∈insert x (x₁ ∷ xs) | no ¬p | (yes p) = here
-- ∈insert x (x₁ ∷ xs) | no ¬p₁ | (no ¬p) = there (∈insert x xs)
--
--
-- ∈sortRemDups : ∀ {x xs} -> x ∈ sortRemDups (x ∷ xs)
-- ∈sortRemDups {x} {[]} = here
-- ∈sortRemDups {x} {x₁ ∷ xs} = ∈insert x (insert x₁ (sortRemDups xs))
--
--
-- ∈trans : ∀ {x ys zs} -> x ∈ ys -> ys ⊆ zs -> x ∈ zs
-- ∈trans here (cons x∈zs ys⊆zs) = x∈zs
-- ∈trans (there x∈ys) (cons _ ys⊆zs) = ∈trans x∈ys ys⊆zs
--
--
-- ⊆trans : ∀ {xs ys zs} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
-- ⊆trans nil ys⊆zs = nil
-- ⊆trans (cons x₁ xs⊆ys) ys⊆zs = cons (∈trans x₁ ys⊆zs) (⊆trans xs⊆ys ys⊆zs)
--
--
-- insert-insert-swap : ∀ x x' ys -> insert x (insert x' ys) ≡ insert x' (insert x ys)
-- insert-insert-swap x x' [] with x ≟ x'
-- insert-insert-swap x .x [] | yes refl with x ≟ x
-- insert-insert-swap x .x [] | yes refl | yes refl = refl
-- insert-insert-swap x .x [] | yes refl | no x≠x = ⊥-elim (x≠x refl)
-- insert-insert-swap x x' [] | no x≠x' with x ≤? x'
-- insert-insert-swap x x' [] | no x≠x' | yes x<x' with x' ≟ x
-- insert-insert-swap x .x [] | no x≠x' | yes x<x' | (yes refl) = ⊥-elim (x≠x' refl)
-- insert-insert-swap x x' [] | no x≠x' | yes x<x' | (no x'≠x) with x' ≤? x
-- insert-insert-swap x x' [] | no x≠x' | yes x<x' | (no x'≠x) | (yes x'<x) = {! p  !}
-- insert-insert-swap x x' [] | no x≠x' | yes x<x' | no _ | no _ = refl
-- insert-insert-swap x x' [] | no x≠x' | (no ¬p) with x' ≟ x
-- insert-insert-swap x .x [] | no x≠x' | (no ¬p) | (yes refl) = ⊥-elim (x≠x' refl)
-- insert-insert-swap x x' [] | no x≠x' | (no ¬p₁) | (no ¬p) with x' ≤? x
-- insert-insert-swap x x' [] | no x≠x' | (no ¬p₁) | (no ¬p) | (yes p) = refl
-- insert-insert-swap x x' [] | no x≠x' | (no x>x') | (no x'≠x) | (no x'>x) = {! ¬p  !}
-- insert-insert-swap x x' (y ∷ ys) with x' ≟ y
-- insert-insert-swap x x' (.x' ∷ ys) | yes refl with x ≟ x'
-- insert-insert-swap .x' x' (.x' ∷ ys) | yes refl | yes refl with x' ≟ x'
-- insert-insert-swap .x' x' (.x' ∷ ys) | yes refl | yes refl | yes refl = refl
-- insert-insert-swap .x' x' (.x' ∷ ys) | yes refl | yes refl | no x'≠x' = ⊥-elim (x'≠x' refl)
-- insert-insert-swap x x' (.x' ∷ ys) | yes refl | no x≠x' = {!   !}
-- insert-insert-swap x x' (y ∷ ys) | no x'≠y = {! ¬p   !}
--
-- --
-- -- insert-insert-swap x .x [] | yes refl with x ≤? x
-- -- insert-insert-swap x .x [] | yes refl | yes _ = refl
-- -- insert-insert-swap x .x [] | yes refl | no _ = refl
-- -- insert-insert-swap x x' [] | no x≠x' with x ≤? x'
-- -- insert-insert-swap x x' [] | no x≠x' | yes _ with x' ≤? x
-- -- insert-insert-swap x x' [] | no x≠x' | (yes x≤x') | (yes x'≤x) = {!   !} -- contradiction
-- -- insert-insert-swap x x' [] | no x≠x' | (yes x≤x') | (no x'>x) with x ≟ x'
-- -- insert-insert-swap x x' [] | no x≠x' | (yes x≤x') | (no x'>x) | (yes p) = {!   !} -- contradiction
-- -- insert-insert-swap x x' [] | no x≠x' | (yes x≤x') | (no x'>x) | (no ¬p) = refl
-- -- insert-insert-swap x x' [] | no x≠x' | no x>x' with x' ≤? x
-- -- insert-insert-swap x x' [] | no x≠x' | (no x>x') | (yes x'≤x) with x' ≟ x
-- -- insert-insert-swap x x' [] | no x≠x' | (no x>x') | (yes x'≤x) | (yes p) = {!   !} -- contradiction
-- -- insert-insert-swap x x' [] | no x≠x' | (no x>x') | (yes x'≤x) | no _ = refl
-- -- insert-insert-swap x x' [] | no x≠x' | (no x>x') | (no x'>x) = {!   !} -- contradiction
-- --
-- -- insert-insert-swap x x' (y ∷ ys) with x ≟ x'
-- -- insert-insert-swap x .x (y ∷ ys) | yes refl with x ≟ y
-- -- insert-insert-swap x .x (.x ∷ ys) | yes refl | yes refl = refl
-- -- insert-insert-swap x .x (y ∷ ys) | yes refl | no x≠y = refl
-- -- insert-insert-swap x x' (y ∷ ys) | no x≠x' with x' ≟ y
-- -- insert-insert-swap x x' (.x' ∷ ys) | no x≠x' | (yes refl) = {!   !}
-- -- insert-insert-swap x x' (y ∷ ys) | no x≠x' | (no x'≠y) = {!   !}
--
--
--
--
-- ∈insert' : ∀ {x x' xs} -> x ∈ xs -> x ∈ insert x' xs
-- ∈insert' {x} {x'} x∈xs = {!   !}
-- -- ∈insert' {x} {x'} here with x' ≤? x
-- -- ∈insert' {x} {x'} here | yes _ with x' ≟ x
-- -- ∈insert' {x} {x'} here | yes _ | yes _ = here
-- -- ∈insert' {x} {x'} here | yes _ | no _ = there here
-- -- ∈insert' {x} {x'} here | no _ = here
-- -- ∈insert' {x} {x'} {y ∷ ys} (there x∈xs) with x' ≤? y
-- -- ∈insert' {x} {x'} {y ∷ ys} (there x∈xs) | yes _ with x' ≟ y
-- -- ∈insert' {x} {x'} {y ∷ ys} (there x∈xs) | yes _ | yes _ = there x∈xs
-- -- ∈insert' {x} {x'} {y ∷ ys} (there x∈xs) | yes _ | no _ = there (there x∈xs)
-- -- ∈insert' {x} {x'} {y ∷ ys} (there x∈xs) | no _ = there (∈insert' x∈xs)
--
--
-- ⊆insert' : ∀ {x xs ys} -> xs ⊆ ys -> xs ⊆ insert x ys
-- ⊆insert' = {!   !}
--
--
--
-- ⊆insert : ∀ x {xs ys} -> xs ⊆ ys -> insert x xs ⊆ insert x ys
-- ⊆insert x {[]} {ys} nil = cons (∈insert x ys) nil
-- ⊆insert x {x' ∷ xs} {ys} (cons x₂ xs⊆ys) with x ≤? x'
-- ⊆insert x {x' ∷ xs} {ys} (cons x₂ xs⊆ys) | yes _ with x ≟ x'
-- ⊆insert .x' {x' ∷ xs} {ys} (cons _ xs⊆ys) | yes _ | yes refl = cons (∈insert x' ys) (⊆insert' xs⊆ys)
-- ⊆insert x {x' ∷ xs} {ys} (cons x₂ xs⊆ys) | yes x≤x' | (no x≠x') = {!   !} --cons (∈insert x ys) (cons {!   !} (⊆insert' xs⊆ys)) -- (x' ∷ xs) ⊆ ys
-- ⊆insert x {x' ∷ xs} {ys} (cons x₂ xs⊆ys) | no x>x' = {!   !} --cons (∈insert' x₂) (⊆insert x xs⊆ys)
--
--
-- ⊆∷ : ∀ x {xs ys} -> xs ⊆ ys -> xs ⊆ (x ∷ ys)
-- ⊆∷ x nil = nil
-- ⊆∷ x (cons x₂ xs⊆ys) = cons (there x₂) (⊆∷ x xs⊆ys)
--
-- ⊆refl : ∀ {xs} -> xs ⊆ xs
-- ⊆refl {[]} = nil
-- ⊆refl {x ∷ xs} = cons here (⊆∷ x ⊆refl)
--
-- ⊆sortRemDups-aux : ∀ x xs -> xs ⊆ insert x xs
-- ⊆sortRemDups-aux x [] = nil
-- ⊆sortRemDups-aux x (x₁ ∷ xs) = cons aux aux₁
--   where
--     aux : x₁ ∈ insert x (x₁ ∷ xs)
--     -- aux with x ≤? x₁
--     -- aux | yes p with x ≟ x₁
--     -- aux | yes _ | yes refl = here
--     -- aux | yes _ | no _ = there here
--     -- aux | no _ = here
--     aux = {!   !}
--
--     aux₁ : xs ⊆ insert x (x₁ ∷ xs)
--     -- aux₁ with x ≤? x₁
--     -- aux₁ | yes _ with x ≟ x₁
--     -- aux₁ | yes _ | yes _ = ⊆∷ x₁ ⊆refl
--     -- aux₁ | yes _ | no _ = ⊆∷ x (⊆∷ x₁ ⊆refl)
--     -- aux₁ | no _ = ⊆∷ x₁ (⊆sortRemDups-aux x xs)
--     aux₁ = {!   !}
--
-- ⊆sortRemDups : ∀ {xs} -> xs ⊆ sortRemDups xs
-- ⊆sortRemDups {[]} = nil
-- ⊆sortRemDups {x ∷ xs} = cons (∈sortRemDups {x} {xs}) (⊆trans ⊆sortRemDups (⊆sortRemDups-aux x (sortRemDups xs)))




open import IO

main = run (putStrLn "Hello, world!")

-- lemma : B (All (All ((Funion 0 0) ∧ (Funion 1 1)))) ⊢ B (All (All ((Funion 0 1) ∧ (Funion 1 0))))
-- lemma = ?
