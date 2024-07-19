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

_v∘v_ : Vars Γ Δ → Vars Θ Γ → Vars Θ Δ
ε v∘v ys = ε
(xs , x) v∘v ys = (xs v∘v ys) , (x v[ ys ]v)

_v∘_ : Vars Γ Δ → Tms Θ Γ → Tms Θ Δ
ε v∘ us = ε
(xs , x) v∘ us = (xs v∘ us) , (x v[ us ])
-- define using vars→tms ?

_∘v_ : Tms Γ Δ → Vars Θ Γ → Tms Θ Δ
ε ∘v xs = ε
(ts , t) ∘v xs = (ts ∘v xs) , (t [ xs ]v)
-- define using vars→tms ?

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

-- code duplication
idv-[]v : t [ idv ]v ≡ t
idv-[]v = {!!}

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

-- not needed?
v[v∘v] : x v[ xs ]v v[ ys ]v ≡ x v[ xs v∘v ys ]v
v[v∘v] {x = zero} {xs = xs , x} = refl
v[v∘v] {x = suc x} {xs = xs , y} = v[v∘v] {x = x}

v[∘] : x v[ ts ] [ us ] ≡ x v[ ts ∘ us ]
v[∘] {x = zero} {ts = ts , t} = refl
v[∘] {x = suc x} {ts = ts , t} = v[∘] {x = x}

[v∘v]v : u [ xs ]v [ ys ]v ≡ u [ xs v∘v ys ]v
[v∘v]v {u = var x} = {!!}
[v∘v]v {u = t $ u} = {!!}
[v∘v]v {u = ƛ u} = {!!}


[v∘]v : u [ xs ]v [ ts ] ≡ u [ xs v∘ ts ]
[v∘]v {u = var x} = {!!}
[v∘]v {u = t $ u} = {!!}
[v∘]v {u = ƛ u} = {!!}

[∘v]v : u [ ts ] [ xs ]v ≡ u [ ts ∘v xs ]
[∘v]v {u = var x} = {!!}
[∘v]v {u = t $ u} = {!!}
[∘v]v {u = ƛ u} = {!!}

suc-vars-lem : suc-vars xs v∘ (ts , t) ≡ xs v∘ ts
suc-vars-lem {xs = ε} = refl
suc-vars-lem {xs = xs , x} = cong₂ _,_ suc-vars-lem refl

idvl : (idv {Γ = Γ}) v∘ ts ≡ ts
idvl {•} {ts = ε} = refl
idvl {Γ ▷ σ} {ts = ts , t} = cong (λ us → us , t)
   (suc-vars idv v∘ (ts , t)
    ≡⟨ suc-vars-lem ⟩
    idv v∘ ts
    ≡⟨ idvl {ts = ts} ⟩
   ts  ∎)

suc-tm-lem : suc-tm u [ ts , t ] ≡ u [ ts ]
suc-tm-lem {u = u}{ts = ts}{t = t} = 
  suc-tm u [ ts , t ]
    ≡⟨⟩
   u [ suc-vars idv ]v [ ts , t ]
    ≡⟨ [v∘]v {u = u}⟩
   u [ (suc-vars idv) v∘ (ts , t) ]
    ≡⟨ cong (λ us → u [ us ]) suc-vars-lem ⟩
   u [ idv v∘ ts ]
    ≡⟨ cong (λ us → u [ us ]) idvl ⟩        
  u [ ts ] ∎

suc-tms-lem : suc-tms us ∘ (ts , t) ≡ us ∘ ts
suc-tms-lem {us = ε} = refl
suc-tms-lem {us = us , u} = cong₂ _,_ (suc-tms-lem {us = us}) (suc-tm-lem {u = u})

suc-var-tms : (x v[ suc-tms {σ = σ} us ]) ≡ suc-tm (x v[ us ]) -- not needed?
suc-var-tms = {!!}

suc-tms-eq : suc-tms {σ = σ} us ≡ us ∘v (suc-vars idv)
suc-tms-eq {us = ε} = refl
suc-tms-eq {us = us , u} = cong₂ _,_ (suc-tms-eq {us = us}) refl

suc-vars-nat : t [ suc-vars {σ = σ} xs ]v ≡ suc-tm (t [ xs ]v)
suc-vars-nat {t = var x}{xs = xs} = 
  var (x v[ suc-vars xs ]v)
    ≡⟨ cong var (suc-nat {y = x}) ⟩
  var (suc (x v[ xs ]v))
    ≡⟨ sym (suc-lem {x = x v[ xs ]v}) ⟩    
  suc-tm (var (x v[ xs ]v)) ∎
suc-vars-nat {t = t $ u} = cong₂ _$_ (suc-vars-nat {t = t}) (suc-vars-nat {t = u})
suc-vars-nat {t = ƛ t}{xs = xs} = cong ƛ (
  t [ suc-vars xs ▷-vars ]v
      ≡⟨ {!!} ⟩
  t [ (suc-vars (xs v∘v idv)) ▷-vars ]v  
    ≡⟨ {!!} ⟩
  t [ (xs v∘v suc-vars idv) ▷-vars ]v  
    ≡⟨ {!!} ⟩
  t [ (xs ▷-vars) v∘v (suc-vars idv ▷-vars) ]v
    ≡⟨ sym ([v∘v]v {u = t} ) ⟩
  t [ xs ▷-vars ]v [ suc-vars idv ▷-vars ]v ∎)

suc-tm-nat : (t [ suc-tms {σ = σ} us ]) ≡ suc-tm (t [ us ])
suc-tm-nat {t = t}{us = us} = 
 t [ suc-tms us ]
    ≡⟨ cong (λ vs → t [ vs ]) (suc-tms-eq {us = us}) ⟩
 t [ us ∘v suc-vars idv ]
    ≡⟨ sym ([∘v]v {u = t}) ⟩
 t [ us ] [ suc-vars idv ]v
    ≡⟨ suc-vars-nat {t = t [ us ]} ⟩
 suc-tm (t [ us ] [ idv ]v)
    ≡⟨ cong suc-tm (idv-[]v {t = t [ us ]}) ⟩   
  suc-tm (t [ us ]) ∎

suc-tms-nat : ts ∘ (suc-tms {σ = σ} us) ≡  suc-tms (ts ∘ us)
suc-tms-nat {ts = ε} = refl
suc-tms-nat {ts = ts , t} = cong₂ _,_ (suc-tms-nat {ts = ts}) (suc-tm-nat {t = t})

∘▷-tms : (_▷-tms ts {σ = σ}) ∘ (us ▷-tms) ≡ (ts ∘ us) ▷-tms
∘▷-tms {ts = ts}{us = us} = cong (λ vs → vs , var zero) 
 (suc-tms ts ∘ (us ▷-tms)
    ≡⟨ suc-tms-lem {us = ts} ⟩
 ts ∘ (suc-tms us)
    ≡⟨ suc-tms-nat {ts = ts} ⟩    
 suc-tms (ts ∘ us) ∎)

[∘] : u [ ts ] [ us ] ≡ u [ ts ∘ us ]
[∘] {u = var x} = v[∘] {x = x}
[∘] {u = t $ u} = cong₂ _$_ ([∘] {u = t}) ([∘] {u = u})
[∘] {u = ƛ u}{ts = ts}{us = us} = cong ƛ (
  u [ ts ▷-tms ] [ us ▷-tms ]
    ≡⟨ [∘] {u = u} ⟩
  u [ (ts ▷-tms) ∘ (us ▷-tms) ]
    ≡⟨ cong (λ vs → u [ vs ]) (∘▷-tms {ts = ts}) ⟩    
  u [ (ts ∘ us) ▷-tms ]  ∎)

idl : id ∘ ts ≡ ts
idl {ts = ε} = refl
idl {ts = ts , t} = cong (λ us → us , t)
   (suc-tms id ∘ (ts , t)
    ≡⟨ suc-tms-lem ⟩
    id ∘ ts
    ≡⟨ idl {ts = ts} ⟩
   ts  ∎)

idr : ts ∘ id ≡ ts
idr {ts = ε} = refl
idr {ts = ts , t} = cong₂ _,_ (idr {ts = ts}) id-[]

{-
 ?
    ≡⟨ ? ⟩
 ? ∎
-}
