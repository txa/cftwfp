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
  suc : Var Γ σ → {τ : Ty} → Var (Γ ▷ τ) σ

variable x y z : Var Γ σ

data Tm : Con → Ty → Set where
  var : Var Γ σ → Tm Γ σ
  _$_ : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ƛ : Tm (Γ ▷ σ) τ → Tm Γ (σ ⇒ τ) 

variable t u v : Tm Γ σ

data _* (X :  Con → Ty → Set) : Con → Con → Set where
  ε : (X *) Γ •
  _,_ : (X *) Γ Δ → X Γ σ → (X *) Γ (Δ ▷ σ)

{-# INJECTIVE_FOR_INFERENCE _* #-}
-- doesn't work

variable X Y Z : Con → Ty → Set

map : ({σ : Ty} → X Γ σ → Y Δ σ) → (X *) Γ Θ → (Y *) Δ Θ
map f ε = ε
map f (xs , x) = map f xs , f x

module S (X : Con → Ty → Set)
         (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
         (sucX : ∀ {Γ}{σ} → X Γ σ → {τ : Ty} → X (Γ ▷ τ) σ)
         (Var→X : ∀ {Γ}{σ} → Var Γ σ → X Γ σ)
         (X→Tm :  ∀ {Γ}{σ} → X Γ σ → Tm Γ σ)
         (Var→X-zero : ∀ {Γ}{σ} → (zeroX {Γ}{σ}) ≡ Var→X zero)
         (Var→X-suc : ∀ {Γ}{σ}{τ}{x : Var Γ σ} → sucX (Var→X x) {τ = τ} ≡ Var→X (suc x))
         (Var→X→Tm : ∀ {Γ}{σ}{x : Var Γ σ} → X→Tm (Var→X x) ≡ var x)
         where

  variable xs ys zs : (X *) Γ Δ
  variable vs ws : (Var *) Γ Δ
  variable ts us : (Tm *) Γ Δ

  Var*→X* : (Var *) Γ Δ → (X *) Γ Δ
  Var*→X* = map Var→X

  X*→Tm* : (X *) Γ Δ → (Tm *) Γ Δ
  X*→Tm* = map X→Tm

  sucX* : {Γ Δ : Con} → (X *) Γ Δ → {τ : Ty} → (X *) (Γ ▷ τ) Δ
  sucX* xs {τ = τ} = map (λ x → sucX x {τ}) xs

  _▷X : {Γ Δ : Con} →  (X *) Γ Δ → {σ : Ty} → (X *) (Γ ▷ σ) (Δ ▷ σ)
  xs ▷X = sucX* xs , zeroX

  idX : {Γ : Con} → (X *) Γ Γ
  idX {Γ = •} = ε
  idX {Γ = Γ ▷ σ} = idX {Γ = Γ} ▷X

  _v[_] : Var Γ σ → (X *) Δ Γ → X Δ σ
  zero v[ xs , x ] = x
  suc y v[ xs , x ] = y v[ xs ]

  suc-nat : x v[ sucX* xs {τ = τ} ] ≡ sucX (x v[ xs ])
  suc-nat {x = zero} {xs = xs , x} = refl
  suc-nat {x = suc x} {xs = xs , _} = suc-nat {x = x}

  v[id] : x v[ idX ] ≡ Var→X x
  v[id] {x = zero} = Var→X-zero
  v[id] {x = suc x} = 
    suc x v[ idX ]
      ≡⟨⟩
    x v[ sucX* idX ]    
      ≡⟨ suc-nat {x = x} ⟩
    sucX (x v[ idX ])    
      ≡⟨ cong (λ y → sucX y) (v[id] {x = x}) ⟩
    sucX (Var→X x)    
      ≡⟨ Var→X-suc ⟩        
    Var→X (suc x) ∎

  _v∘_ : ∀ {Γ}{Δ} → (Var *) Γ Θ → (X *) Δ Γ → (X *) Δ Θ
  xs v∘ ys = map (λ x → x v[ ys ]) xs

  v∘id : ∀ {xs : (Var *) Γ Δ} → xs v∘ idX ≡ Var*→X* xs
  v∘id {xs = ε} = refl
  v∘id {xs = xs , x} = cong₂ _,_ (v∘id {xs = xs}) v[id]

  -- idv : (Var *) Γ Γ
  -- Var*→X* idv ≡ idX
  -- idv∘ : idv v∘ xs ≡ xs   

  -- x v[ vs v∘ xs ] ≡ x v[ Var*→X* vs ] ?[ xs ]
  -- Var→X y ≡ x v[ Var*→X* vs ] → x v[ vs v∘ xs ] ≡ y v[ xs ]

  -- (vs v∘ ws) v∘ xs
  -- Var*→X* vsws ≡ vs v∘ (Var*→X* ws) → vsws v∘ xs ≡ vs ∘v (ws ∘v xs)    

  _[_] : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
  var x [ xs ] = X→Tm (x v[ xs ])
  (t $ u) [ xs ] = (t [ xs ]) $ (u [ xs ])
  ƛ t [ xs ] = ƛ (t [ xs ▷X ])

  [id] : t [ idX ] ≡ t
  [id] {t = var x} = 
    X→Tm (x v[ idX ])
      ≡⟨ cong X→Tm (v[id] {x = x}) ⟩
    X→Tm (Var→X x)
      ≡⟨ Var→X→Tm ⟩      
    var x ∎
  [id] {t = t $ u} = cong₂ _$_ ([id] {t = t}) ([id] {t = u})
  [id] {t = ƛ t} = cong ƛ ([id] {t = t})

  _∘_ : (Tm *) Γ Θ → (X *) Δ Γ → (Tm *) Δ Θ
  ts ∘ ys = map (λ t → t [ ys ]) ts

  -- idt : (Tm *) Γ Γ
  -- X*→Tm* idX ≡ idt
  -- id∘ : idt ∘ xs ≡ X*→Tm* xs

  ∘id : ts ∘ idX ≡ ts
  ∘id {ts = ε} = refl
  ∘id {ts = ts , t} = cong₂ _,_ (∘id {ts = ts}) ([id] {t = t})

module V where

  open S Var zero suc (λ x → x) var refl refl refl

  suc-tm : Tm Γ σ → {τ : Ty} → Tm (Γ ▷ τ) σ
  suc-tm t = t [ sucX* idX ]

  suc-tm-var : suc-tm (var x) {τ} ≡ var (suc x)
  suc-tm-var {x = x} = 
    suc-tm (var x)
      ≡⟨⟩
    (var x) [ sucX* idX ]
      ≡⟨⟩
    var (x v[ sucX* idX ])
      ≡⟨⟩
    var ((suc x) v[ idX ])
      ≡⟨ cong var (v[id] {x = suc x}) ⟩          
    var (suc x) ∎

open S Tm (var zero) V.suc-tm var (λ x → x) refl V.suc-tm-var refl public

