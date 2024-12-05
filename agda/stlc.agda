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

suc-vars : Vars Γ Δ → {σ : Ty} → Vars (Γ ▷ σ) Δ
suc-vars ε = ε
suc-vars (xs , x) = (suc-vars xs) , (suc x)

_▷-vars : Vars Γ Δ → {σ : Ty} → Vars (Γ ▷ σ) (Δ ▷ σ)
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

suc-tms : Tms Γ Δ → {σ : Ty} → Tms (Γ ▷ σ) Δ
suc-tms ε = ε
suc-tms (ts , t) = (suc-tms ts) , (suc-tm t)

_▷-tms : Tms Γ Δ → {σ : Ty} → Tms (Γ ▷ σ) (Δ ▷ σ)
xs ▷-tms = (suc-tms xs) , var zero

_v[_] : Var Γ σ → Tms Δ Γ → Tm Δ σ
zero v[ vs , v ] = v
suc y v[ vs , v ] = y v[ vs ]

_[_] : Tm Γ σ → Tms Δ Γ → Tm Δ σ
var x [ vs ] = x v[ vs ]
(t $ u) [ vs ] = (t [ vs ]) $ (u [ vs ])
ƛ t [ xs ] = ƛ (t [ xs ▷-tms ])

id : Tms Γ Γ
id {Γ = •} = ε
id {Γ = Γ ▷ σ} = id {Γ = Γ} ▷-tms

_∘_ : Tms Γ Δ → Tms Θ Γ → Tms Θ Δ
ε ∘ us = ε
(ts , t) ∘ us = (ts ∘ us) , (t [ us ])

--- verification
vars→tms : Vars Γ Δ → Tms Γ Δ
vars→tms ε = ε
vars→tms (xs , x) = vars→tms xs , var x

-- renamings

_v∘v_ : Vars Γ Δ → Vars Θ Γ → Vars Θ Δ
ε v∘v ys = ε
(xs , x) v∘v ys = (xs v∘v ys) , (x v[ ys ]v)

v[v∘v]v : x v[ xs ]v v[ ys ]v ≡ x v[ xs v∘v ys ]v
v[v∘v]v {x = zero} {xs = xs , x} = refl
v[v∘v]v {x = suc x} {xs = xs , y} = v[v∘v]v {x = x}

suc-vars-lem : suc-vars xs v∘v (ys , y) ≡ xs v∘v ys
suc-vars-lem {xs = ε} = refl
suc-vars-lem {xs = xs , x} = cong₂ _,_ suc-vars-lem refl

suc-var-nat : y v[ suc-vars xs {σ = σ} ]v ≡ suc (y v[ xs ]v)
suc-var-nat {y = zero}{xs = xs , x}  = refl
suc-var-nat {y = suc y}{xs = xs , x}  = suc-var-nat {y = y}

suc-vars-nat : xs v∘v suc-vars ys {σ = σ} ≡ suc-vars (xs v∘v ys)
suc-vars-nat {xs = ε} = refl
suc-vars-nat {xs = xs , x} = cong₂ _,_ (suc-vars-nat {xs = xs}) (suc-var-nat {y = x})

∘▷-vars : (_▷-vars xs {σ = σ}) v∘v (ys ▷-vars) ≡ (xs v∘v ys) ▷-vars
∘▷-vars {xs = xs}{ys = ys} = 
 (xs ▷-vars) v∘v (ys ▷-vars)
    ≡⟨⟩
 (suc-vars xs , zero) v∘v (suc-vars ys , zero)
    ≡⟨ cong (λ zs → zs , zero) (suc-vars-lem {xs = xs}) ⟩
 (xs v∘v suc-vars ys) , zero
    ≡⟨ cong (λ zs → zs , zero) suc-vars-nat ⟩     
 (xs v∘v ys) ▷-vars ∎

[v∘v]v : u [ xs ]v [ ys ]v ≡ u [ xs v∘v ys ]v
[v∘v]v {u = var x} = cong var (v[v∘v]v {x = x})
[v∘v]v {u = t $ u} = cong₂ _$_ ([v∘v]v {u = t}) ([v∘v]v {u = u})
[v∘v]v {u = ƛ u}{xs = xs}{ys = ys} = cong ƛ (
 u [ xs ▷-vars ]v [ ys ▷-vars ]v
    ≡⟨ [v∘v]v {u = u} ⟩
 u [ (xs ▷-vars) v∘v (ys ▷-vars) ]v
    ≡⟨ cong (λ zs → u [ zs ]v) (∘▷-vars {xs = xs}{ys = ys}) ⟩
 u [ (xs v∘v ys) ▷-vars ]v ∎)

v[idv]v : x v[ idv ]v ≡ x
v[idv]v {x = zero} = refl
v[idv]v {x = suc x} = 
  (suc x v[ idv ]v)
    ≡⟨⟩
  x v[ suc-vars idv ]v
    ≡⟨ suc-var-nat {y = x} ⟩
  suc (x v[ idv ]v) 
    ≡⟨ cong suc v[idv]v ⟩
  suc x ∎

[idv]v : t [ idv ]v ≡ t
[idv]v {t = var x} = cong var v[idv]v
[idv]v {t = t $ u} = cong₂ _$_ ([idv]v {t = t}) ([idv]v {t = u})
[idv]v {t = ƛ t} = cong ƛ ([idv]v {t = t})

idvl : {xs : Vars Θ Γ} → idv v∘v xs ≡ xs
idvl {xs = ε} = refl
idvl {xs = xs , x} = cong (λ ys → ys , x) (
  suc-vars idv v∘v (xs , x)
    ≡⟨ suc-vars-lem ⟩
  idv v∘v xs
    ≡⟨ idvl ⟩    
  xs ∎)

idvr : xs v∘v idv ≡ xs
idvr {xs = ε} = refl
idvr {xs = xs , x} = cong₂ _,_ (idvr {xs = xs}) v[idv]v

v∘v-assoc : (xs v∘v ys) v∘v zs ≡ xs v∘v (ys v∘v zs)
v∘v-assoc {xs = ε} = refl
v∘v-assoc {xs = xs , x} = cong₂ _,_ (v∘v-assoc {xs = xs}) (v[v∘v]v {x = x})

-- substitution

_v∘_ : Vars Γ Δ → Tms Θ Γ → Tms Θ Δ
ε v∘ ts = ε
(xs , x) v∘ ts = (xs v∘ ts) , (x v[ ts ])

-- duplication of suc-vars-lem
suc-vars-tms-lem : suc-vars xs v∘ (ts , t) ≡ xs v∘ ts
suc-vars-tms-lem {xs = ε} = refl
suc-vars-tms-lem {xs = xs , x} = cong₂ _,_ suc-vars-tms-lem refl

-- duplication of idvl-tms
idvl-tms : idv v∘ ts ≡ ts
idvl-tms {ts = ε} = refl
idvl-tms {ts = ts , t} = cong (λ us → us , t) (
  suc-vars idv v∘ (ts , t)
    ≡⟨ suc-vars-tms-lem ⟩
  idv v∘ ts
    ≡⟨ idvl-tms ⟩    
  ts ∎)

-- everything is duplicated, refactor!
v[v∘] : x v[ xs ]v v[ ts ] ≡ x v[ xs v∘ ts ]
v[v∘] {x = zero} {xs = xs , y} = refl
v[v∘] {x = suc x} {xs = xs , y} = v[v∘] {x = x}

suc-var-tm-nat : x v[ suc-tms ts {σ = σ} ] ≡ suc-tm (x v[ ts ])
suc-var-tm-nat {x = zero} {ts = ts , t} = refl
suc-var-tm-nat {x = suc x} {ts = ts , t} = suc-var-tm-nat {x = x}

suc-vars-tms-nat : xs v∘ (suc-tms ts {σ = σ}) ≡ suc-tms (xs v∘ ts)
suc-vars-tms-nat {xs = ε} = refl
suc-vars-tms-nat {xs = xs , x} =
  cong₂ _,_ (suc-vars-tms-nat {xs = xs}) (suc-var-tm-nat {x = x})

v∘▷ : (_▷-vars xs {σ = σ}) v∘ (ts ▷-tms) ≡ (xs v∘ ts) ▷-tms
v∘▷ {xs = xs}{ts = ts} = 
 (xs ▷-vars) v∘ (ts ▷-tms)
    ≡⟨⟩
 (suc-vars xs , zero) v∘ (suc-tms ts , var zero)
    ≡⟨ cong (λ zs → zs , var zero) (suc-vars-tms-lem {xs = xs}) ⟩
 (xs v∘ suc-tms ts) , var zero
    ≡⟨ cong (λ zs → zs , var zero) (suc-vars-tms-nat {xs = xs}) ⟩     
 (xs v∘ ts) ▷-tms ∎

[v∘] : u [ xs ]v [ ts ] ≡ u [ xs v∘ ts ]
[v∘] {u = var x} = v[v∘] {x = x}
[v∘] {u = t $ u} = cong₂ _$_ ([v∘] {u = t}) ([v∘] {u = u})
[v∘] {u = ƛ u}{xs = xs}{ts = ts} = cong ƛ (
 u [ xs ▷-vars ]v [ ts ▷-tms ]
    ≡⟨ [v∘] {u = u} ⟩
 u [ (xs ▷-vars) v∘ (ts ▷-tms) ]
    ≡⟨ cong (λ zs → u [ zs ]) (v∘▷ {xs = xs}) ⟩
 u [ (xs v∘ ts) ▷-tms ] ∎)
  
suc-tm-lem : suc-tm t [ us , u ] ≡ t [ us ]
suc-tm-lem {t = t}{us = us}{u = u} = 
  suc-tm t [ us , u ]
    ≡⟨⟩
  t [ suc-vars idv ]v [ us , u ]
    ≡⟨ [v∘] {u = t} ⟩
  t [ (suc-vars idv) v∘ (us , u) ]
    ≡⟨ cong (λ vs → t [ vs ]) suc-vars-tms-lem ⟩
  t [ idv v∘ us ]
    ≡⟨ cong (λ vs → t [ vs ]) idvl-tms ⟩        
 t [ us ] ∎

suc-tms-lem : suc-tms ts ∘ (us , u) ≡ ts ∘ us
suc-tms-lem {ts = ε} = refl
suc-tms-lem {ts = ts , t} = cong₂ _,_ (suc-tms-lem {ts = ts}) (suc-tm-lem {t = t})

-- needs [∘]v

_∘v_ : Tms Γ Δ → Vars Θ Γ → Tms Θ Δ
ε ∘v ts = ε
(ts , t) ∘v xs = (ts ∘v xs) , (t [ xs ]v)

id∘vl : ts ∘v idv ≡ ts
id∘vl {ts = ε} = refl
id∘vl {ts = ts , t} = cong₂ _,_ (id∘vl {ts = ts}) ([idv]v {t = t})

suc-tm-vars-lem : suc-tm t [ xs , x ]v ≡ t [ xs ]v
suc-tm-vars-lem {t = t}{xs = xs}{x = x} = 
  suc-tm t [ xs , x ]v
    ≡⟨⟩
  t [ suc-vars idv ]v [ xs , x ]v
    ≡⟨ [v∘v]v {u = t} ⟩
  t [ (suc-vars idv) v∘v (xs , x) ]v
    ≡⟨ cong (λ ys → t [ ys ]v) (suc-vars-lem {xs = idv}) ⟩
  t [ idv v∘v xs ]v
    ≡⟨ cong (λ ys → t [ ys ]v) (idvl {xs = xs}) ⟩        
 t [ xs ]v ∎

suc-tms-vars-lem : suc-tms ts ∘v (xs , x) ≡ ts ∘v xs
suc-tms-vars-lem {ts = ε} {xs = xs} = refl
suc-tms-vars-lem {ts = ts , t} {xs = xs} = cong₂ _,_ (suc-tms-vars-lem {ts = ts}) (suc-tm-vars-lem {t = t})

suc-tm-var-nat : t [ suc-vars xs {σ = σ} ]v ≡ suc-tm (t [ xs ]v)
suc-tm-var-nat {t = t}{xs = xs} = 
   t [ suc-vars xs ]v
     ≡⟨ cong (λ ys → t [ suc-vars ys ]v) (sym (idvr {xs = xs})) ⟩
   t [ suc-vars (xs v∘v idv) ]v   
     ≡⟨ cong (λ ys → t [ ys ]v) (sym (suc-vars-nat {xs = xs})) ⟩
   t [ xs v∘v (suc-vars idv) ]v
     ≡⟨ sym ([v∘v]v {u = t}) ⟩     
   t [ xs ]v [ suc-vars idv ]v
     ≡⟨⟩
   suc-tm (t [ xs ]v) ∎

suc-tms-vars-nat : ts ∘v (suc-vars xs {σ = σ}) ≡ suc-tms (ts ∘v xs)
suc-tms-vars-nat {ts = ε} = refl
suc-tms-vars-nat {ts = ts , t} = cong₂ _,_ (suc-tms-vars-nat {ts = ts}) (suc-tm-var-nat {t = t})

∘v▷ : (_▷-tms ts {σ = σ}) ∘v (xs ▷-vars) ≡ (ts ∘v xs) ▷-tms
∘v▷ {ts = ts}{xs = xs} = 
 (ts ▷-tms) ∘v (xs ▷-vars)
    ≡⟨⟩
 (suc-tms ts , var zero) ∘v (suc-vars xs , zero)
    ≡⟨ cong (λ us → us , var zero) (suc-tms-vars-lem {ts = ts}) ⟩
 (ts ∘v suc-vars xs) , var zero
    ≡⟨ cong (λ us → us , var zero) (suc-tms-vars-nat {ts = ts}) ⟩     
 (ts ∘v xs) ▷-tms ∎

v[∘v] : x v[ ts ] [ xs ]v ≡ x v[ ts ∘v xs ]
v[∘v] {x = zero} {ts = ts , t} = refl
v[∘v] {x = suc x} {ts = ts , t} = v[∘v] {x = x}

[∘v] : u [ ts ] [ xs ]v ≡ u [ ts ∘v xs ]
[∘v] {u = var x} = v[∘v] {x = x}
[∘v] {u = t $ u} = cong₂ _$_ ([∘v] {u = t}) ([∘v] {u = u})
[∘v] {u = ƛ u}{ts = ts}{xs = xs} = cong ƛ ((
 u [ ts ▷-tms ] [ xs ▷-vars ]v
    ≡⟨ [∘v] {u = u} ⟩
 u [ (ts ▷-tms) ∘v (xs ▷-vars) ]
    ≡⟨ cong (λ zs → u [ zs ]) (∘v▷ {ts = ts}) ⟩
 u [ (ts ∘v xs) ▷-tms ] ∎))

suc-tm-nat : t [ suc-tms ts {σ = σ} ] ≡ suc-tm (t [ ts ])
suc-tm-nat{t = t}{ts = ts} = 
 t [ suc-tms ts ]
     ≡⟨ sym (cong (λ us → t [ suc-tms us ]) (id∘vl {ts = ts})) ⟩
 t [ suc-tms (ts ∘v idv) ]
     ≡⟨ sym (cong (λ us → t [ us ]) (suc-tms-vars-nat {ts = ts})) ⟩     
 t [ ts ∘v (suc-vars idv) ]  
     ≡⟨ sym ([∘v] {u = t}) ⟩
 t [ ts ] [ suc-vars idv ]v 
    ≡⟨⟩
 suc-tm (t [ ts ]) ∎


suc-tms-nat : ts ∘ (suc-tms us {σ = σ}) ≡ suc-tms (ts ∘ us)
suc-tms-nat {ts = ε} = refl
suc-tms-nat {ts = ts , t} =
  cong₂ _,_ (suc-tms-nat {ts = ts}) (suc-tm-nat {t = t})

∘▷-tms : (_▷-tms ts {σ = σ}) ∘ (us ▷-tms) ≡ (ts ∘ us) ▷-tms
∘▷-tms {ts = ts}{us = us} = (ts ▷-tms) ∘ (us ▷-tms)
    ≡⟨⟩
 (suc-tms ts , var zero) ∘ (suc-tms us , var zero)
    ≡⟨ cong (λ vs → vs , var zero) suc-tms-lem ⟩
 (ts ∘ suc-tms us) , var zero
    ≡⟨ cong (λ vs → vs , var zero) suc-tms-nat ⟩     
 (ts ∘ us) ▷-tms ∎

v[∘] : x v[ ts ] [ us ] ≡ x v[ ts ∘ us ]
v[∘] {x = zero} {ts = ts , t} = refl
v[∘] {x = suc x} {ts = ts , t} = v[∘] {x = x}

[∘] : u [ ts ] [ us ] ≡ u [ ts ∘ us ]
[∘] {u = var x} = v[∘] {x = x}
[∘] {u = t $ u} = cong₂ _$_ ([∘] {u = t}) ([∘] {u = u})
[∘] {u = ƛ u}{ts = ts}{us = us} = cong ƛ (
 u [ ts ▷-tms ] [ us ▷-tms ]
    ≡⟨ [∘] {u = u} ⟩
 u [ (ts ▷-tms) ∘ (us ▷-tms) ]
    ≡⟨ cong (λ vs → u [ vs ]) (∘▷-tms {ts = ts}{us = us}) ⟩
 u [ (ts ∘ us) ▷-tms ] ∎)

v[id] : x v[ id ] ≡ var x
v[id] {x = zero} = refl
v[id] {x = suc x} = 
  x v[ suc-tms id ]
     ≡⟨ {!!} ⟩
  suc-tm (x v[ id ])
     ≡⟨ {!!} ⟩     
  var (suc x) ∎


[id] : t [ id ] ≡ t
[id] {t = var x} = v[id] {x = x}
[id] {t = t $ u} = cong₂ _$_ ([id] {t = t}) ([id] {t = u})
[id] {t = ƛ t} = cong ƛ ([id] {t = t})


idr : ts ∘ id ≡ ts
idr {ts = ε} = refl
idr {ts = ts , t} = cong₂ _,_ (idr {ts = ts}) {!!}

∘-assoc : (ts ∘ us) ∘ vs ≡ ts ∘ (us ∘ vs)
∘-assoc {ts = ε} = refl
∘-assoc {ts = ts , t} = cong₂ _,_ (∘-assoc {ts = ts}) ([∘] {u = t})

{-
 ?
    ≡⟨ ? ⟩
 ? ∎
-}
