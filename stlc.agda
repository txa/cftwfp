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

variable x y z : Var Γ σ

data Tm : Con → Ty → Set where
  var : Var Γ σ → Tm Γ σ
  _$_ : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ƛ : Tm (Γ ▷ σ) τ → Tm Γ (σ ⇒ τ) 

variable t u v : Tm Γ σ

data Vars : Con → Con → Set where
  ε : Vars Γ •
  _,_ : Vars Γ Δ → Var Γ σ → Vars Γ (Δ ▷ σ)

variable xs ys zs : Vars Δ Γ

data Tms : Con → Con → Set where
  ε : Tms Γ •
  _,_ : Tms Γ Δ → Tm Γ σ → Tms Γ (Δ ▷ σ)

variable ts us vs : Tms Δ Γ

suc-vars : Vars Γ Δ → Vars (Γ ▷ σ) Δ
suc-vars ε = ε
suc-vars (xs , x) = (suc-vars xs) , (suc x)

_▷-vars : Vars Γ Δ → Vars (Γ ▷ σ) (Δ ▷ σ)
xs ▷-vars = (suc-vars xs) , zero

idv : Vars Γ Γ
idv {Γ = •} = ε
idv {Γ = Γ ▷ σ} = idv {Γ = Γ} ▷-vars 

_v[_]v : Var Γ σ → Vars Δ Γ → Var Δ σ
zero v[ xs , x ]v = x
suc y v[ xs , x ]v = y v[ xs ]v

_[_]v : Tm Γ σ → Vars Δ Γ → Tm Δ σ
var x [ xs ]v = var (x v[ xs ]v)
(t $ u) [ xs ]v = (t [ xs ]v) $ (u [ xs ]v)
ƛ t [ xs ]v = ƛ (t [ xs ▷-vars ]v)

suc-tm : Tm Γ σ → Tm (Γ ▷ τ) σ
suc-tm t = t [ suc-vars idv ]v

suc-tms : Tms Γ Δ → Tms (Γ ▷ σ) Δ
suc-tms ε = ε
suc-tms (ts , t) = (suc-tms ts) , (suc-tm t)

_▷-tms : Tms Γ Δ → Tms (Γ ▷ σ) (Δ ▷ σ)
xs ▷-tms = (suc-tms xs) , var zero

_v[_] : Var Γ σ → Tms Δ Γ → Tm Δ σ
zero v[ vs , v ] = v
suc y v[ vs , v ] = y v[ vs ]

_[_] : Tm Γ σ → Tms Δ Γ → Tm Δ σ
var x [ vs ] = x v[ vs ]
(t $ u) [ vs ] = (t [ vs ]) $ (u [ vs ])
ƛ t [ xs ] = ƛ (t [ xs ▷-tms ])

vars→tms : Vars Γ Δ → Tms Γ Δ
vars→tms ε = ε
vars→tms (xs , x) = vars→tms xs , var x

id : Tms Γ Γ
id {Γ = •} = ε
id {Γ = Γ ▷ σ} = id {Γ = Γ} ▷-tms

_∘_ : Tms Γ Δ → Tms Θ Γ → Tms Θ Δ
ε ∘ us = ε
(ts , t) ∘ us = (ts ∘ us) , (t [ us ])

--- verification

suc-nat : {y : Var Γ τ} → y v[ suc-vars {σ = σ} xs ]v ≡ suc (y v[ xs ]v)
suc-nat {xs = xs , x} {zero} = refl
suc-nat {xs = xs , x} {suc y} = suc-nat {y = y}

idv-lem : x v[ idv ]v ≡ x
idv-lem {x = zero} = refl
idv-lem {x = suc x} = 
  (suc x v[ idv ]v)
    ≡⟨⟩
  x v[ suc-vars idv ]v
    ≡⟨ suc-nat {y = x} ⟩
  suc (x v[ idv ]v) 
    ≡⟨ cong suc idv-lem ⟩
  suc x ∎

suc-lem : suc-tm {τ = τ} (var x) ≡ var (suc x)
suc-lem  {x = x}= 
  suc-tm (var x)
    ≡⟨⟩
   var (x v[ suc-vars idv ]v)   
    ≡⟨ cong var (suc-nat {y = x}) ⟩
  var (suc (x v[ idv ]v))   
    ≡⟨ cong (λ y → var (suc y)) idv-lem ⟩    
  var (suc x) ∎

sucs-lem : suc-tms {σ = σ} (vars→tms xs) ≡ vars→tms (suc-vars xs)
sucs-lem {xs = ε} = refl
sucs-lem {xs = xs , x} = cong₂ _,_ (sucs-lem {xs = xs}) (suc-lem {x = x})

idv-id : {Γ : Con} → vars→tms (idv {Γ = Γ}) ≡ id
idv-id {•} = refl
idv-id {Γ ▷ σ} = cong (λ ts → ts , var zero)
  (vars→tms (suc-vars idv)
    ≡⟨ sym (sucs-lem {xs = idv}) ⟩
  suc-tms (vars→tms idv)
    ≡⟨ cong suc-tms (idv-id {Γ = Γ}) ⟩    
   suc-tms id  ∎)

vars-nat : y v[ vars→tms xs ] ≡ var (y v[ xs ]v)
vars-nat {y = zero} {xs = xs , x} = refl
vars-nat {y = suc y} {xs = xs , x} = vars-nat {y = y}

id-[] : {t : Tm Γ σ} → t [ id ] ≡ t
id-[] {t = var x} = 
   x v[ id ]
    ≡⟨ cong (λ ts → x v[ ts ]) (sym idv-id) ⟩
   x v[ vars→tms idv ]
    ≡⟨ vars-nat {y = x} ⟩
   var (x v[ idv ]v)
    ≡⟨ cong var idv-lem ⟩
  var x ∎  
id-[] {t = t $ u} = cong₂ _$_ (id-[]{t = t}) (id-[] {t = u})
id-[] {t = ƛ t} = cong ƛ (id-[] {t = t})


{-
 ?
    ≡⟨ ? ⟩
 ? ∎
-}
