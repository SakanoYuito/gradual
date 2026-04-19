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
    TyFun   : Ty → Ty → Ty
    Ty*     : Ty

Context = List Ty

data Lookup : Context → ℕ → Ty → Set where
    L-Z : ∀ {Γ T} → Lookup (T ∷ Γ) zero T
    L-S : ∀ {Γ n T S} → Lookup Γ n T → Lookup (S ∷ Γ) (suc n) T

data fun[_]=_ : Ty → Ty → Set where
    match-fun : ∀ {T11 T12}
                → fun[ (TyFun T11 T12) ]= (TyFun T11 T12)
    match-*   : fun[ Ty* ]= (TyFun Ty* Ty*)

data BTy : Ty → Set where
    BTy-Nat  : BTy TyNat
    BTy-Bool : BTy TyBool

data Term : Set where
    tm-true : Term
    tm-false : Term
    tm-zero : Term
    tm-inc  : Term → Term
    tm-var  : ℕ → Term
    tm-fun  : Ty → Term → Term
    tm-app  : Term → Term → Label → Term

-- data NConst : Term → Set where
--     nc-zero : NConst tm-zero
--     nc-inc  : ∀ {t}
--             → NConst t
--             → NConst (tm-inc t)

-- data BConst : Term → Set where
--     bc-false : BConst tm-false
--     bc-true  : BConst tm-true

-- data FConst : Term → Set where
--     fc-fun   : ∀ {T t} → FConst (tm-fun T t)

-- data Const : Term → Set where
--     NConst-is-Const : ∀ {v} → NConst v → Const v
--     BConst-is-Const : ∀ {v} → BConst v → Const v
--     FConst-is-Const : ∀ {v} → FConst v → Const v

data _~_ : Ty → Ty → Set where
    *-consistent-L : ∀ {T} → Ty* ~ T
    *-consistent-R : ∀ {T} → T ~ Ty*
    BTy-consistent : ∀ {T} → BTy T → T ~ T
    fun-consistent : ∀ {T1 T2 T3 T4}
                    → T1 ~ T3
                    → T2 ~ T4
                    → (TyFun T1 T2) ~ (TyFun T3 T4)

_ : (TyFun TyNat Ty*) ~ (TyFun TyNat TyBool)
_ = fun-consistent (BTy-consistent BTy-Nat) *-consistent-L

data _⊢_::_ : Context → Term → Ty → Set where
    T-True  : ∀ {Γ} → Γ ⊢ tm-true  :: TyBool
    T-False : ∀ {Γ} → Γ ⊢ tm-false :: TyBool
    T-Zero  : ∀ {Γ} → Γ ⊢ tm-zero  :: TyNat
    T-Inc   : ∀ {t1 Γ}
                → Γ ⊢ t1 :: TyNat
                → Γ ⊢ (tm-inc t1) :: TyNat
    T-Var   : ∀ {Γ x T}
                → Lookup Γ x T
                → Γ ⊢ (tm-var x) :: T
    T-Fun   : ∀ {Γ t T1 T2}
                → (T1 ∷ Γ) ⊢ t :: T2
                → Γ ⊢ (tm-fun T1 t) :: (TyFun T1 T2)
    T-App   : ∀ {Γ t1 t2 T1 T2 T11 T12 l}
                → Γ ⊢ t1 :: T1 
                → Γ ⊢ t2 :: T2 
                → fun[ T1 ]= (TyFun T11 T12)
                → T2 ~ T11 
                → Γ ⊢ (tm-app t1 t2 l) :: T12


-- cast insersion

data GTy : Ty → Set where
    GTy-BTy  : ∀ {T} → BTy T → GTy T
    GTy-fun* : GTy (TyFun Ty* Ty*)

data Term' : Set where
    tm'-true  : Term'
    tm'-false : Term'
    tm'-zero  : Term'
    tm'-inc   : Term' → Term'
    tm'-var   : ℕ → Term'
    tm'-fun   : Ty → Term' → Term'
    tm'-app   : Term' → Term' → Term'
    tm'-cast  : Term' → Ty → Ty → Label → Term'
    tm'-blame : Ty → Label → Term'

data NVal : Term' → Set where
    nv-zero : NVal tm'-zero
    nv-inc  : ∀ {t}
            → NVal t
            → NVal (tm'-inc t)
            
data Val : Term' → Set where
    NVal-is-Val  : ∀ {t} → NVal t → Val t
    True-is-Val  : Val tm'-true
    False-is-Val : Val tm'-false
    Fun-is-Val   : ∀ {t T} → Val (tm'-fun T t)
    Cast-Fun-is-Val : ∀ {v T1 T2 T3 T4 l}
                        → Val v 
                        → Val (tm'-cast v (TyFun T1 T2) (TyFun T3 T4) l)
    Cast-Inj-is-Val : ∀ {v T l}
                        → Val v 
                        → GTy T
                        → Val (tm'-cast v T Ty* l)

data Result : Term' → Set where
    Value : ∀ {v}
            → Val v 
            → Result v
    Blame : ∀ {T l}
            → Result (tm'-blame T l)

data _⊢C_::_ : Context → Term' → Ty → Set where
    T'-True  : ∀ {Γ} → Γ ⊢C tm'-true  :: TyBool
    T'-False : ∀ {Γ} → Γ ⊢C tm'-false :: TyBool
    T'-Zero  : ∀ {Γ} → Γ ⊢C tm'-zero  :: TyNat
    T'-Inc   : ∀ {t1 Γ}
                → Γ ⊢C t1 :: TyNat
                → Γ ⊢C (tm'-inc t1) :: TyNat
    T'-Var   : ∀ {Γ x T}
                → Lookup Γ x T
                → Γ ⊢C (tm'-var x) :: T
    T'-Fun   : ∀ {Γ t T1 T2}
                → (T1 ∷ Γ) ⊢C t :: T2
                → Γ ⊢C (tm'-fun T1 t) :: (TyFun T1 T2)
    T-App   : ∀ {Γ t1 t2 T1 T2 T11 T12}
                → Γ ⊢C t1 :: T1 
                → Γ ⊢C t2 :: T2 
                → fun[ T1 ]= (TyFun T11 T12)
                → T2 ~ T11 
                → Γ ⊢C (tm'-app t1 t2) :: T12
    T-Cast  : ∀ {Γ t T1 T2 l}
                → Γ ⊢C t :: T1 
                → T1 ~ T2 
                → Γ ⊢C (tm'-cast t T1 T2 l) :: T2
    T-Blame : ∀ {Γ T l}
                → Γ ⊢C (tm'-blame T l) :: T 

data _⊢_~>_::_ : Context → Term → Term' → Ty → Set where
    C-true  : ∀ {Γ} → Γ ⊢ tm-true  ~> tm'-true  :: TyBool
    C-false : ∀ {Γ} → Γ ⊢ tm-false ~> tm'-false :: TyBool
    C-zero  : ∀ {Γ} → Γ ⊢ tm-zero  ~> tm'-zero  :: TyNat
    C-inc   : ∀ {Γ t t'}
                → Γ ⊢ t ~> t' :: TyNat 
                → Γ ⊢ (tm-inc t) ~> (tm'-inc t') :: TyNat
    C-Var   : ∀ {Γ x T}
                → Lookup Γ x T
                → Γ ⊢ (tm-var x) ~> (tm'-var x) :: T
    C-Fun   : ∀ {Γ t t' T1 T2}
                → (T1 ∷ Γ) ⊢ t ~> t' :: T2
                → Γ ⊢ (tm-fun T1 t) ~> (tm'-fun T1 t') :: T2
    C-App   : ∀ {Γ t1 t2 t1' t2' T1 T2 T11 T12 l}
                → Γ ⊢ t1 ~> t1' :: T1
                → Γ ⊢ t2 ~> t2' :: T2
                → fun[ T1 ]= (TyFun T11 T12)
                → T2 ~ T11
                → Γ ⊢ (tm-app t1 t2 l)
                    ~> tm'-app 
                        (tm'-cast t1' T1 (TyFun T11 T12) l)
                        (tm'-cast t2' T2 T11             l) :: T12

data _↦_ : Term' → Term' → Set where
    E-Beta   : ∀ {T t v}
                → Val v
                → (tm'-app (tm'-fun T t) v) ↦ {!   !}
    E-IdBase : ∀ {v B l}
                → Val v 
                → BTy B 
                → (tm'-cast v B B l) ↦ v
    E-Id*    : ∀ {v l}
                → Val v 
                → (tm'-cast v Ty* Ty* l) ↦ v 
    E-Cast-Succeed : ∀ {v G l1 l2}
                → Val v
                → GTy G
                → (tm'-cast (tm'-cast v G Ty* l1) Ty* G l2) ↦ v
    E-Cast-Fail : ∀ {v G1 G2 l1 l2}
                → Val v
                → GTy G1
                → GTy G2
                → G1 ≢ G2
                → (tm'-cast (tm'-cast v G1 Ty* l1) Ty* G2 l2) ↦ (tm'-blame G2 l2)
    E-AppCast : ∀ {v1 v2 T1 T2 T3 T4 l}
                → Val v1
                → Val v2
                → tm'-app (tm'-cast v1 (TyFun T1 T2) (TyFun T3 T4) l) v2
                    ↦ tm'-cast (tm'-app v1 (tm'-cast v2 T3 T1 l)) T2 T4 l
    E-Ground  : ∀ {v T G l}
                → Val v
                → GTy G
                → T ≢ Ty*
                → T ≢ G
                → T ~ G
                → tm'-cast v T Ty* l
                    ↦ tm'-cast (tm'-cast v T G l) G Ty* l
    E-Expand  : ∀ {v T G l}
                → Val v 
                → GTy G
                → T ≢ Ty*
                → T ≢ G
                → T ~ G
                → tm'-cast v Ty* T l
                    ↦ tm'-cast (tm'-cast v Ty* G l) G T l
    