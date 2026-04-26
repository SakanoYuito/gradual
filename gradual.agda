module Gradual where

open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; cong; trans)
open import Data.Nat using (ℕ; zero; suc; _<?_; _+_; _≟_; _∸_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Bool
open import Relation.Nullary
open import Data.List using (List; []; _∷_)

Label : Set
Label = ℕ

data Ty : Set where
    TyNat   : Ty
    TyBool  : Ty
    _⇒_     : Ty → Ty → Ty
    Ty*     : Ty

data BTy : Ty → Set where
    BTyNat  : BTy TyNat
    BTyBool : BTy TyBool

Context = List Ty

data _∋_ : Context → Ty → Set where
    Z : ∀ {Γ A}   → (A ∷ Γ) ∋ A
    S : ∀ {Γ A B} → Γ ∋ A → (B ∷ Γ) ∋ A

infix 2 fun[_]=_
data fun[_]=_ : Ty → Ty → Set where
    match⇒ : ∀ {A B}
            → fun[ A ⇒ B ]= A ⇒ B
    match* : fun[ Ty* ]= Ty* ⇒ Ty*

data _~_ : Ty → Ty → Set where
    consistent-L* : ∀ {T} → Ty* ~ T
    consistent-R* : ∀ {T} → T ~ Ty*
    consistent-B  : ∀ {B} → BTy B → B ~ B
    consistent-⇒  : ∀ {T1 T2 T3 T4}
                    → T1 ~ T3
                    → T2 ~ T4
                    → (T1 ⇒ T2) ~ (T3 ⇒ T4)

~refl : ∀ {T} → T ~ T
~refl {TyNat} = consistent-B BTyNat
~refl {TyBool} = consistent-B BTyBool
~refl {t ⇒ t₁} = consistent-⇒ ~refl ~refl
~refl {Ty*} = consistent-L*

fun-to-consistent : ∀ {T T11 T12} → fun[ T ]= (T11 ⇒ T12) → T ~ (T11 ⇒ T12)
fun-to-consistent match⇒ = ~refl
fun-to-consistent match* = consistent-L*


infixl 5 [_·_]_
infixr 7 ƛ_
infix 4 _⊢_
data _⊢_ : Context → Ty → Set where
    V      : ∀ {Γ A}
        → Γ ∋ A
        → Γ ⊢ A
    ƛ_     : ∀ {Γ A B}
        → (A ∷ Γ) ⊢ B
        → Γ ⊢ (A ⇒ B)
    [_·_]_ : ∀ {Γ T1 T11 T12 T2}
        → Γ ⊢ T1
        → Γ ⊢ T2
        → fun[ T1 ]= (T11 ⇒ T12)
        → T2 ~ T11
        → Label
        → Γ ⊢ T12

    tm-true  : ∀ {Γ} → Γ ⊢ TyBool
    tm-false : ∀ {Γ} → Γ ⊢ TyBool
    -- tm-if    : ∀ {Γ T}
    --         → Γ ⊢ TyBool
    --         → Γ ⊢ T
    --         → Γ ⊢ T
    --         → Γ ⊢ T
    
    tm-zero    : ∀ {Γ} → Γ ⊢ TyNat
    tm-succ    : ∀ {Γ}
            → Γ ⊢ TyNat
            → Γ ⊢ TyNat
    tm-pred    : ∀ {Γ}
            → Γ ⊢ TyNat
            → Γ ⊢ TyNat
    tm-iszero  : ∀ {Γ}
            → Γ ⊢ TyNat
            → Γ ⊢ TyBool


-- cast insersion

data GTy : Ty → Set where
    GTy-BTy : ∀ {T} → BTy T → GTy T
    GTy-*⇒* : GTy (Ty* ⇒ Ty*)

data _⊢C_ : Context → Ty → Set where
    VC     : ∀ {Γ A}
        → Γ ∋ A
        → Γ ⊢C A
    ƛC_     : ∀ {Γ A B}
        → (A ∷ Γ) ⊢C B
        → Γ ⊢C (A ⇒ B)
    [_·C_] : ∀ {Γ T1 T11 T12 T2}
        → Γ ⊢C T1
        → Γ ⊢C T2
        → fun[ T1 ]= (T11 ⇒ T12)
        → T2 ~ T11
        → Γ ⊢C T12

    tmC-true  : ∀ {Γ} → Γ ⊢C TyBool
    tmC-false : ∀ {Γ} → Γ ⊢C TyBool
    -- tmC-if    : ∀ {Γ T}
    --         → Γ ⊢C TyBool
    --         → Γ ⊢C T
    --         → Γ ⊢C T
    --         → Γ ⊢C T
    
    tmC-zero    : ∀ {Γ} → Γ ⊢C TyNat
    tmC-succ    : ∀ {Γ}
            → Γ ⊢C TyNat
            → Γ ⊢C TyNat
    tmC-pred    : ∀ {Γ}
            → Γ ⊢C TyNat
            → Γ ⊢C TyNat
    tmC-iszero  : ∀ {Γ}
            → Γ ⊢C TyNat
            → Γ ⊢C TyBool
    
    tmC-cast  : ∀ {Γ T1 T2}
            → Γ ⊢C T1
            → T1 ~ T2
            → Label
            → Γ ⊢C T2
    tmC-blame : ∀ {Γ T}
            → Label
            → Γ ⊢C T

translate : ∀ {Γ A} → Γ ⊢ A → Γ ⊢C A 
translate (V x) = VC x
translate (ƛ t) = ƛC (translate t)
translate (([ t1 · t2 ] m) c l) = {!   !}
translate tm-true = tmC-true
translate tm-false = tmC-false
translate tm-zero = tmC-zero
translate (tm-succ t) = tmC-succ (translate t)
translate (tm-pred t) = tmC-pred (translate t)
translate (tm-iszero t) = tmC-iszero (translate t)