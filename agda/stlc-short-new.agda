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

module S(X : Con → Ty → Set)
        (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (sucX : ∀ {Γ}{σ} → X Γ σ → {τ : Ty} → X (Γ ▷ τ) σ)
        (_[_]X : ∀ {Γ}{σ}{Δ} → X Γ σ → (X *) Δ Γ → X Δ σ)
        (zeroX≡ : ∀ {Γ}{Δ}{σ}{xs : (X *) Δ Γ}{x : X Δ σ}
            → zeroX [ xs , x ]X ≡ x)
        (sucX≡ : ∀ {Γ}{Δ}{σ}{τ}{y : X Γ τ}{xs : (X *) Δ Γ}{x : X Δ σ}
            → (sucX y) [ xs , x ]X ≡ y [ xs ]X) where

   sucX* : {Γ Δ : Con} → (X *) Γ Δ → {τ : Ty} → (X *) (Γ ▷ τ) Δ
   sucX* xs {τ = τ} = map (λ x → sucX x {τ}) xs

   _▷X : {Γ Δ : Con} →  (X *) Γ Δ → {σ : Ty} → (X *) (Γ ▷ σ) (Δ ▷ σ)
   xs ▷X = sucX* xs , zeroX

   idX : {Γ : Con} → (X *) Γ Γ
   idX {Γ = •} = ε
   idX {Γ = Γ ▷ σ} = idX {Γ = Γ} ▷X

   _∘X_ : (X *) Γ Θ → (X *) Δ Γ → (X *) Δ Θ
   xs ∘X ys = map (λ i → i [ ys ]X) xs

module V(X : Con → Ty → Set) where

  _v[_] : Var Γ σ → (X *) Δ Γ → X Δ σ
  zero v[ xs , x ] = x
  suc y v[ xs , x ] = y v[ xs ]

module VV where

  open V Var public
  open S Var zero suc _v[_] refl refl public
  
module T(X : Con → Ty → Set)
        (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (sucX : ∀ {Γ}{σ} → X Γ σ → {τ : Ty} → X (Γ ▷ τ) σ)
        (_[_]X : ∀ {Γ}{σ}{Δ} → X Γ σ → (X *) Δ Γ → X Δ σ)
        (zeroX≡ : ∀ {Γ}{Δ}{σ}{xs : (X *) Δ Γ}{x : X Δ σ}
            → zeroX [ xs , x ]X ≡ x)
        (sucX≡ : ∀ {Γ}{Δ}{σ}{τ}{y : X Γ τ}{xs : (X *) Δ Γ}{x : X Δ σ}
            → (sucX y) [ xs , x ]X ≡ y [ xs ]X) where
        (X→Tm :  ∀ {Γ}{σ} → X Γ σ → Tm Γ σ) where

  open VV using (_v[_])


  _[_] : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
  var x [ xs ] = X→Tm (x v[ xs ])
  (t $ u) [ xs ] = (t [ xs ]) $ (u [ xs ])
  ƛ t [ xs ] = ƛ (t [ xs ▷X ])
  


{-
   sucX*∘X : {ys : (X *) Γ Δ}{y : X Γ τ}
           → sucX* xs {τ = τ} ∘X (ys , y) ≡ xs ∘X ys
   sucX*∘X {xs = ε} = refl
   sucX*∘X {xs = xs , x} = cong₂ _,_ ( sucX*∘X {xs = xs}) (sucX≡ {y = x})

   module N (sucX-nat : ∀ {Γ}{Δ}{σ}{τ}{xs : (X *) Δ Γ}{x : X Γ σ} → x [ sucX* xs {τ = τ} ]X ≡ sucX (x [ xs ]X)) where

     sucX*-nat : xs ∘X (sucX* ys {τ = τ}) ≡ sucX* (xs ∘X ys)
     sucX*-nat {xs = ε} = refl
     sucX*-nat {xs = xs , x} = cong₂ _,_ (sucX*-nat {xs = xs}) (sucX-nat {x = x})

     ∘▷X : (_▷X xs {σ = σ}) ∘X (ys ▷X) ≡ (xs ∘X ys) ▷X 
     ∘▷X {xs = xs}{ys = ys} = 
       (xs ▷X) ∘X (ys ▷X)
         ≡⟨⟩
       (sucX* xs , zeroX) ∘X (sucX* ys , zeroX)
         ≡⟨ cong₂ _,_ (sucX*∘X {xs = xs}) zeroX≡ ⟩     
       (xs ∘X sucX* ys) , zeroX
         ≡⟨ cong (λ zs → zs , zeroX) (sucX*-nat {xs = xs}) ⟩     
       (xs ∘X ys) ▷X ∎

       -- module T(


open V Var

open S Var zero suc _v[_] refl refl



{-

     open V X -- inline ?

     _[_] : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
     var x [ vs ] = x v[ vs ]
     (t $ u) [ vs ] = (t [ vs ]) $ (u [ vs ])
     ƛ t [ xs ] = ƛ (t [ xs ▷X ])
-}
{-
module VV = V Var
module VT = V Tm

module SV = S Var zero suc VV._v[_] refl refl

module TV where

  --open SV renaming (_[_]X to _v[_]v)
  


  _[_] : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
  var x [ vs ] = x v[ vs ]
  (t $ u) [ vs ] = (t [ vs ]) $ (u [ vs ])
  ƛ t [ xs ] = ƛ (t [ xs ▷X ])
-}

  

{-
  suc-tm : Tm Γ σ → {τ : Ty} → Tm (Γ ▷ τ) σ
  suc-tm t = t [ sucX* idX ]
-}


{-
module S (X : Con → Ty → Set)
         (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
         (sucX : ∀ {Γ}{σ} → X Γ σ → {τ : Ty} → X (Γ ▷ τ) σ)
         (Var→X : ∀ {Γ}{σ} → Var Γ σ → X Γ σ)
         (X→Tm :  ∀ {Γ}{σ} → X Γ σ → Tm Γ σ)
         (Var→X-zero : ∀ {Γ}{σ} → (zeroX {Γ}{σ}) ≡ Var→X zero)
         (Var→X-suc : ∀ {Γ}{σ}{τ}{x : Var Γ σ} → sucX (Var→X x) {τ = τ} ≡ Var→X (suc x))
         (Var→X→Tm : ∀ {Γ}{σ}{x : Var Γ σ} → X→Tm (Var→X x) ≡ var x)
         where

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


-}
-}
