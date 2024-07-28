open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public

data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

variable σ τ : Ty

data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con

variable Γ Δ Θ : Con

data Var : Con → Ty → Set where
  zero : Var (Γ ▷ σ) σ
  suc : Var Γ σ → Var (Γ ▷ τ) σ

variable i j k : Var Γ σ

data Tm : Con → Ty → Set where
  var : Var Γ σ → Tm Γ σ
  _$_ : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ƛ : Tm (Γ ▷ σ) τ → Tm Γ (σ ⇒ τ) 

variable t u v : Tm Γ σ

data _* (X :  Con → Ty → Set) : Con → Con → Set where
  ε : (X *) Γ •
  _,_ : (X *) Γ Δ → X Γ σ → (X *) Γ (Δ ▷ σ)

variable X Y Z : Con → Ty → Set
variable x y z : X Γ σ
variable xs ys zs : (X *) Γ Δ
variable is js ks : (Var *) Γ Δ
variable ts us vs : (Tm *) Γ Δ

map : ({σ : Ty} → X Γ σ → Y Δ σ) → (X *) Γ Θ → (Y *) Δ Θ
map f ε = ε
map f (xs , x) = map f xs , f x

module S(X Y : Con → Ty → Set)
        (_[_] : ∀ {Γ}{σ}{Δ} → X Γ σ → (Y *) Δ Γ → Y Δ σ) where

   _∘_ : (X *) Γ Θ → (Y *) Δ Γ → (Y *) Δ Θ
   xs ∘ ys = map (λ x → x [ ys ]) xs

module W(X : Con → Ty → Set)
        (zero : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (suc : ∀ {Γ}{σ}{τ} → X Γ σ → X (Γ ▷ τ) σ) where

   suc* : {Γ Δ : Con} → (X *) Γ Δ → (X *) (Γ ▷ τ) Δ
   suc* xs = map (λ x → suc x) xs

   _▷* : {Γ Δ : Con} →  (X *) Γ Δ → {σ : Ty} → (X *) (Γ ▷ σ) (Δ ▷ σ)
   xs ▷* = suc* xs , zero

   id : {Γ : Con} → (X *) Γ Γ
   id {Γ = •} = ε
   id {Γ = Γ ▷ σ} = id {Γ = Γ} ▷*

   module WW (Y : Con → Ty → Set)
             (_[_] : ∀ {Γ}{σ}{Δ} → X Γ σ → (Y *) Δ Γ → Y Δ σ)
             (zero≡ : ∀ {Γ}{σ}{Δ}
                 {ys : (Y *) Δ Γ}{y : Y Δ σ}
                 → zero [ ys , y ] ≡ y)
             (suc≡ : ∀ {Γ}{σ}{τ}{Δ}
                     {ys : (Y *) Δ Γ}{y : Y Δ σ}{x : X Γ τ}
                     → (suc x) [ ys , y ] ≡ x [ ys ]) where

       open S X Y _[_]

       suc*∘ : {ys : (Y *) Δ Γ}{y : Y Δ τ}
          → (suc* {τ = τ} xs) ∘ (ys , y) ≡ xs ∘ ys
       suc*∘ {xs = ε} = refl
       suc*∘ {xs = xs , x} = cong₂ _,_ (suc*∘ {xs = xs}) (suc≡ {x = x})

       idl : {Γ : Con}{ys : (Y *) Δ Γ} → (id {Γ = Γ}) ∘ ys ≡ ys
       idl {Γ = •} {ε} = refl
       idl {Γ = Γ ▷ σ} {ys , y} = cong₂ _,_ (
         suc* id ∘ (ys , y)
         ≡⟨ suc*∘ ⟩
         id ∘ ys
         ≡⟨ idl ⟩    
         ys ∎
         ) zero≡
       
module V(X : Con → Ty → Set)
        (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (sucX : ∀ {Γ}{σ}{τ} → X Γ σ → X (Γ ▷ τ) σ)
        (Var→X : ∀ {Γ}{σ} → Var Γ σ → X Γ σ)
        (Var→X-zero : ∀ {Γ}{σ} → (zeroX {Γ}{σ}) ≡ Var→X zero)
        (Var→X-suc : ∀ {Γ}{σ}{τ}{x : Var Γ σ} →
                   sucX {τ = τ} (Var→X x) ≡ Var→X (suc x))
        where

  _v[_] : Var Γ σ → (X *) Δ Γ → X Δ σ
  zero v[ xs , x ] = x
  (suc i) v[ xs , x ] = i v[ xs ]

  open W X zeroX sucX 
  --open S Var X _v[_]

  suc-nat-v : i v[ suc* {τ = τ} xs ] ≡ sucX (i v[ xs ])
  suc-nat-v {i = zero} {xs = xs , x} = refl
  suc-nat-v {i = suc i} {xs = xs , x} = suc-nat-v {i = i}

  v[id] : i v[ id ] ≡ Var→X i 
  v[id] {i = zero} = Var→X-zero
  v[id] {i = suc i} = 
     (suc i) v[ id ]
        ≡⟨⟩
     i v[ suc* id ]
        ≡⟨ suc-nat-v {i = i} ⟩
     sucX (i v[ id ])
        ≡⟨ cong sucX v[id] ⟩
     sucX (Var→X i)
        ≡⟨ Var→X-suc ⟩           
     Var→X (suc i) ∎

{-
module T(X : Con → Ty → Set)
        (X→Tm :  ∀ {Γ}{σ} → X Γ σ → Tm Γ σ)
        (zero : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (suc : ∀ {Γ}{σ}{τ} → X Γ σ → X (Γ ▷ τ) σ) where

  open V X using (_v[_]) 
  open W X zero suc using (suc*; _▷* ; id) public

  _[_] : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
  var x [ xs ] = X→Tm (x v[ xs ])
  (t $ u) [ xs ] = (t [ xs ]) $ (u [ xs ])
  ƛ t [ xs ] = ƛ (t [ (xs ▷*) ])

open T Var var zero suc renaming
  (_[_] to _[_]v ; id to idv; suc* to sucv*)

suc-tm : Tm Γ σ → Tm (Γ ▷ τ) σ
suc-tm t = t [ sucv* idv ]v -- t [ suc-vars idv ]v

open T Tm (λ x → x) (var zero) suc-tm
open S Tm

   
-}
