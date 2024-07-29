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

{-
module W (X : Con → Ty → Set)
         (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
         (sucX : ∀ {Γ}{σ}{τ} → X Γ σ → X (Γ ▷ τ) σ)
         (_X[_]X : ∀ {Γ}{σ}{Δ} → X Γ σ → (X *) Δ Γ → X Δ σ)
         
       
where
-}


module T(X : Con → Ty → Set)
        (Var→X : ∀ {Γ}{σ} → Var Γ σ → X Γ σ)
        (X→Tm :  ∀ {Γ}{σ} → X Γ σ → Tm Γ σ)
        (Var→X→Tm : ∀ {Γ}{σ}{i : Var Γ σ} → X→Tm (Var→X i) ≡ var i) 
        (zeroX : ∀ {Γ}{σ} → X (Γ ▷ σ) σ)
        (sucX : ∀ {Γ}{σ}{τ} → X Γ σ → X (Γ ▷ τ) σ)
        (Var→X-zero : ∀ {Γ}{σ} → (zeroX {Γ}{σ}) ≡ Var→X zero)
        (Var→X-suc : ∀ {Γ}{σ}{τ}{x : Var Γ σ} →
                   sucX {τ = τ} (Var→X x) ≡ Var→X (suc x))
          where

   _v[_] : Var Γ σ → (X *) Δ Γ → X Δ σ
   zero v[ xs , x ] = x
   (suc i) v[ xs , x ] = i v[ xs ]

   sucX* : {Γ Δ : Con} → (X *) Γ Δ → (X *) (Γ ▷ τ) Δ
   sucX* xs = map (λ x → sucX x) xs

   _▷X : {Γ Δ : Con} →  (X *) Γ Δ → {σ : Ty} → (X *) (Γ ▷ σ) (Δ ▷ σ)
   xs ▷X = sucX* xs , zeroX

   idX : {Γ : Con} → (X *) Γ Γ
   idX {Γ = •} = ε
   idX {Γ = Γ ▷ σ} = idX {Γ = Γ} ▷X

   suc-nat-v : i v[ sucX* {τ = τ} xs ] ≡ sucX (i v[ xs ])
   suc-nat-v {i = zero} {xs = xs , x} = refl
   suc-nat-v {i = suc i} {xs = xs , x} = suc-nat-v {i = i}

   v[id] : i v[ idX ] ≡ Var→X i 
   v[id] {i = zero} = Var→X-zero
   v[id] {i = suc i} = 
      (suc i) v[ idX ]
         ≡⟨⟩
      i v[ sucX* idX ]
         ≡⟨ suc-nat-v {i = i} ⟩
      sucX (i v[ idX ])
         ≡⟨ cong sucX v[id] ⟩
      sucX (Var→X i)
         ≡⟨ Var→X-suc ⟩           
      Var→X (suc i) ∎

   _v∘_ : (Var *) Γ Θ → (X *) Δ Γ → (X *) Δ Θ
   is v∘ xs = map (λ i → i v[ xs ]) is

   _[_]X : Tm Γ σ → (X *) Δ Γ → Tm Δ σ
   var x [ xs ]X = X→Tm (x v[ xs ])
   (t $ u) [ xs ]X = (t [ xs ]X) $ (u [ xs ]X)
   ƛ t [ xs ]X = ƛ (t [ (xs ▷X) ]X)

   t[id]X : t [ idX ]X ≡ t 
   t[id]X {t = var i} = 
      X→Tm (i v[ idX ])
        ≡⟨ cong X→Tm v[id] ⟩
      X→Tm (Var→X i)
        ≡⟨ Var→X→Tm  ⟩       
      var i ∎
   t[id]X {t = t $ u} = cong₂ _$_ (t[id]X {t = t}) (t[id]X {t = u})
   t[id]X {t = ƛ t} = cong ƛ t[id]X

   _∘X_ : (Tm *) Γ Θ → (X *) Δ Γ → (Tm *) Δ Θ
   ts ∘X xs = map (λ t → t [ xs ]X) ts

   ∘Xid : ts ∘X idX ≡ ts
   ∘Xid {ts = ε} = refl
   ∘Xid {ts = ts , t} = cong₂ _,_ (∘Xid {ts = ts}) t[id]X

open T Var (λ i → i) var refl zero suc refl refl renaming (_v[_] to _v[_]v; _[_]X to _[_]v; sucX* to sucVar* ; idX to idv)

suc-tm : Tm Γ σ → Tm (Γ ▷ τ) σ
suc-tm t = t [ sucVar* idv ]v

suc-tm-var : suc-tm {τ = τ} (var i) ≡ var (suc i)
suc-tm-var {i = i} = 
   suc-tm (var i)
    ≡⟨⟩
    var (i v[ sucVar* idv ]v)
    ≡⟨ cong var (suc-nat-v {i = i}) ⟩
    var (suc (i v[ idv ]v))
    ≡⟨ cong (λ i → var (suc i)) v[id] ⟩    
    var (suc i) ∎

open T Tm var (λ t → t) refl (var zero) suc-tm refl suc-tm-var renaming (idX to id ; _∘X_ to _∘_ ; ∘Xid to ∘id)

{-
suc*∘ : {ys : (Y *) Δ Γ}{y : Y Δ τ}
          → (suc* {τ = τ} xs) ∘ (ys , y) ≡ xs ∘ ys
suc*∘ {xs = ε} = refl
suc*∘ {xs = xs , x} = cong₂ _,_ (suc*∘ {xs = xs}) (suc≡ {x = x})
-}




{-
  open S Tm X {!!}
-}

{-
open T Var var zero suc renaming
  (_[_] to _[_]v ; id to idv; suc* to sucv*)

suc-tm : Tm Γ σ → Tm (Γ ▷ τ) σ
suc-tm t = t [ sucv* idv ]v -- t [ suc-vars idv ]v

open T Tm (λ x → x) (var zero) suc-tm
open S Tm

   
-}
{-
   sucX*∘ : {xs : (X *) Δ Γ}{X : Y Δ τ}
      → (sucX* {τ = τ} xs) ∘ (ys , y) ≡ xs ∘ ys
   sucX*∘ {xs = ε} = refl
   sucX*∘ {xs = xs , x} = cong₂ _,_ (sucX*∘ {xs = xs}) (sucX≡ {x = x})
-}
