open import Relation.Binary.PropositionalEquality hiding ([_])

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

data Tm : Con → Ty → Set where
  var : Var Γ σ → Tm Γ σ
  _$_ : Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  ƛ : Tm (Γ ▷ σ) τ → Tm Γ (σ ⇒ τ) 

data Vars : Con → Con → Set where
  ε : Vars Γ •
  _,_ : Vars Γ Δ → Var Γ σ → Vars Γ (Δ ▷ σ)

data Tms : Con → Con → Set where
  ε : Tms Γ •
  _,_ : Tms Γ Δ → Tm Γ σ → Tms Γ (Δ ▷ σ)

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

_++_ : Con → Con → Con
Δ ++ • = Δ
Δ ++ (Γ ▷ σ) = (Δ ++ Γ) ▷ σ


