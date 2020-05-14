open import Data.Bool using (Bool; true; false)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≥_; _>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; [_]; _∷_; _∷ʳ_; _++_)
open import Data.List.Reverse using (Reverse; reverseView)
open import Function using (_$_)

module theorem2 (Addr : Set) (_≟_ : Addr → Addr → Bool) (Data : Set) (MAX_WCNT : ℕ)where

variable
  addr : Addr
  dat  : Data


infixl 20 _•_
infixl 20 _⊙_
infixl 20 _++RTC_
infixl 20 _<≐>_
infixr 100 _[_↦_]

data Action : Set where
  w[_↦_] : (addr : Addr) (dat : Data) → Action
  wᶠ     :                              Action
  f      :                              Action
  r      :                              Action
  wᶜ     :                              Action
  fᶜ     :                              Action
  rᶜ     :                              Action
  cp     :                              Action
  er     :                              Action
  cpᶜ    :                              Action
  erᶜ    :                              Action

variable
  ac : Action

data Regular : Action → Set where
  w  : Regular w[ addr ↦ dat ]
  wᶠ : Regular wᶠ
  cp : Regular cp
  er : Regular er

data Write : Action → Set where
  w  : Write w[ addr ↦ dat ]
  wᶠ : Write wᶠ

data Snapshot : Action → Set where
  f : Snapshot f

data RecoveryCrash : Action → Set where
  rᶜ : RecoveryCrash rᶜ

data RegularSuccess : Action → Set where
  w : RegularSuccess w[ addr ↦ dat ]
  f : RegularSuccess f

data RegularCrash : Action → Set where
  wᶜ  : RegularCrash wᶜ
  fᶜ  : RegularCrash fᶜ
  cpᶜ : RegularCrash cpᶜ
  erᶜ : RegularCrash erᶜ

data Regular×Snapshot : Action → Set where
  w  : Regular×Snapshot w[ addr ↦ dat ]
  wᶠ : Regular×Snapshot wᶠ
  cp : Regular×Snapshot cp
  er : Regular×Snapshot er
  f  : Regular×Snapshot f

data Regular×SnapshotCrash : Action → Set where
  wᶜ  : Regular×SnapshotCrash wᶜ
  cpᶜ : Regular×SnapshotCrash cpᶜ
  erᶜ : Regular×SnapshotCrash erᶜ
  fᶜ  : Regular×SnapshotCrash fᶜ

record State : Set where
  constructor <_,_>
  field
    volatile : Addr → Data
    stable   : Addr → Data
    w-count  : ℕ

variable
  t  : State
  t' : State

_[_↦_] : (Addr → Data) → Addr → Data → (Addr → Data)
(s [ addr ↦ dat ]) i with addr ≟ i
...                  | true  = dat
...                  | false = s i

_≐_ : (Addr → Data) → (Addr → Data) → Set
s ≐ t = ∀ (addr : Addr) → s addr ≡ t addr

sym-≐ : ∀ {s t : Addr → Data} → s ≐ t → t ≐ s
sym-≐ eq = λ{x → sym (eq x)}

_<≐>_ : ∀ {s t u : Addr → Data} → s ≐ t → t ≐ u → s ≐ u
_<≐>_ {s} {t} {u} e q = λ{x → begin s x ≡⟨ e x ⟩ t x ≡⟨ q x ⟩ u x ∎}

data Step (s s' : State) : Action → Set where
  w   : State.w-count s ≤ MAX_WCNT
      → State.volatile s [ addr ↦ dat ] ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → suc (State.w-count s) ≡ State.w-count s'
      → Step s s' w[ addr ↦ dat ]
  wᶠ  : State.w-count s > MAX_WCNT
      → State.volatile s ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → Step s s' wᶠ
  f   : State.volatile s ≐ State.volatile s'
      → State.volatile s ≐ State.stable s'
      → State.w-count s' ≡ zero
      → Step s s' f
  r   : State.stable s ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → State.w-count s' ≡ zero
      → Step s s' r
  wᶜ  : State.stable s ≐ State.stable s'
      → Step s s' wᶜ
  fᶜ  : State.volatile s ≐ State.stable s' ⊎ State.stable s ≐ State.stable s'
      → Step s s' fᶜ
  rᶜ  : State.stable s ≐ State.stable s'
      → Step s s' rᶜ
  cp  : State.volatile s ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → State.w-count s ≡ State.w-count s'
      → Step s s' cp
  er  : State.volatile s ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → State.w-count s ≡ State.w-count s'
      → Step s s' er
  cpᶜ : State.stable s ≐ State.stable s' → Step s s' cpᶜ
  erᶜ : State.stable s ≐ State.stable s' → Step s s' erᶜ

_⟦_⟧▸_ : State → Action → State → Set
s ⟦ ac ⟧▸ s' = Step s s' ac

record StbP (ac : Action) : Set where --Stable Reserving Actions
  field
    preserve : {s s' : State} → s ⟦ ac ⟧▸ s' → (State.stable s ≐ State.stable s')

instance
  stb-r   : StbP r
  stb-r   = record { preserve = λ{(r _ ss _) → ss} }
  stb-w   : StbP w[ addr ↦ dat ]
  stb-w   = record { preserve = λ{(w _ _ ss _ ) → ss} }
  stb-wᶠ  : StbP wᶠ
  stb-wᶠ  = record { preserve = λ{(wᶠ _ _ ss) → ss} }
  stb-wᶜ  : StbP wᶜ
  stb-wᶜ  = record { preserve = λ{(wᶜ ss) → ss} }
  stb-rᶜ  : StbP rᶜ
  stb-rᶜ  = record { preserve = λ{(rᶜ ss) → ss} }
  stb-cp  : StbP cp
  stb-cp  = record { preserve = λ{(cp _ ss _) → ss}}
  stb-er  : StbP er
  stb-er  = record { preserve = λ{(er _ ss _) → ss}}
  stb-cpᶜ : StbP cpᶜ
  stb-cpᶜ = record { preserve = λ{(cpᶜ ss) → ss}}
  stb-erᶜ : StbP erᶜ
  stb-erᶜ = record { preserve = λ{(erᶜ ss) → ss}}

data Fragment : Set where
  []  :                     Fragment
  _•_ : Fragment → Action → Fragment

data F2L : Fragment → List Action → Set where
  empty : F2L [] []
  f2l   : {x : Action} → {ef : Fragment} → {la : List Action} → F2L ef la →  F2L (ef • x) (x ∷ la )

variable
  ef  : Fragment
  ef₁ : Fragment
  ef₂ : Fragment
  ef₃ : Fragment

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → All P xs → P x → All P (x ∷ xs)

mapAll : {A : Set} {P Q : A → Set} {xs : List A} → ({x : A} → P x → Q x) → All P xs → All Q xs
mapAll pq []        = []
mapAll pq (all ∷ x) = (mapAll pq all) ∷ (pq x)

_⊙_ : Fragment → Fragment → Fragment
xs ⊙ []       = xs
xs ⊙ (ys • y) = (xs ⊙ ys) • y


--Recursive Transitive Closure
data RTC {S : Set} (R : S → Action → S → Set) : S → Fragment → S → Set where
  ∅   : ∀ {s : S} → RTC R s [] s
  _•_ : ∀ {s t u : S} {acs : Fragment} {ac : Action}
      → RTC R s acs t → R t ac u → RTC R s (acs • ac) u


_⟦_⟧*▸_ = RTC _⟦_⟧▸_

splitRTC : {S : Set} {R : S → Action → S → Set} {s s' : S} {splitOn rest : Fragment}
         → RTC R s (splitOn ⊙ rest) s' → ∃[ s'' ] (RTC R s splitOn s'' × RTC R s'' rest s')
splitRTC {splitOn = ef₁} {rest = []}                t = (_ , t , ∅)
splitRTC {splitOn = ef₁} {rest = (ef₂ • ac)} (t • rr) = let (s'' , t₁ , t₂) = splitRTC t
                                                        in  (s'' , t₁ , t₂ • rr)

_++RTC_ : {S : Set} {R : S → Action → S → Set} {s t u : S} {ef₁ ef₂ : Fragment}
        → RTC R s ef₁ t → RTC R t ef₂ u → RTC R s (ef₁ ⊙ ef₂) u
tc-s-t ++RTC ∅             = tc-s-t
tc-s-t ++RTC (tc-t-u • rr) = (tc-s-t ++RTC tc-t-u) • rr

idemₛ : ∀ {frag : Fragment} {flist : List Action} → {prf : F2L frag flist} → All StbP flist
      → ∀ {s s' : State} → s ⟦ frag ⟧*▸ s'
      → State.stable s ≐ State.stable s'
idemₛ {prf = empty} [] ∅ = λ{_ → refl}
idemₛ {prf = f2l prf} (all ∷ x) (s2s'' • s''2s') = idemₛ {prf = prf} all s2s'' <≐> StbP.preserve x s''2s'

n→sp : Regular ac → StbP ac
n→sp w  = stb-w
n→sp wᶠ = stb-wᶠ
n→sp cp = stb-cp
n→sp er = stb-er

rᶜ→sp : RecoveryCrash ac → StbP ac
rᶜ→sp rᶜ = stb-rᶜ

lemma2-1 : ∀ {ac : Action} → {{_ : StbP ac}}
         → ∀ {frag-w frag-rᶜ : Fragment} → {flist-w flist-rᶜ : List Action} → {prf₁ : F2L frag-w flist-w } → {prf₂ : F2L frag-rᶜ flist-rᶜ}
         → {{all₁ : All Regular flist-w}} → {{all₂ : All RecoveryCrash flist-rᶜ}}
         → ∀ {s s' : State} → s ⟦ frag-w • ac ⊙ frag-rᶜ ⟧*▸ s'
         → State.stable s ≐ State.stable s'
lemma2-1 {ac = ac} {{du}} {frag-w = frag-w} {frag-rᶜ = frag-rᶜ} {prf₁ = prf₁} {prf₂ = prf₂} {{all₁ = all₁}} {{all₂ = all₂}} s▸s' with splitRTC {splitOn = frag-w • ac} s▸s'
...    | s″ , s▸s″ • x , s″x▸s'  = idemₛ {prf = prf₁} (mapAll n→sp all₁) s▸s″    <≐>
                                   StbP.preserve du x                            <≐>
                                   idemₛ {prf = prf₂} (mapAll rᶜ→sp all₂) s″x▸s'

lemma2-2-f : ∀ {s s' : State} {ef : Fragment} → s ⟦ ef • f ⟧*▸ s' → State.volatile s' ≐ State.stable s'
lemma2-2-f (s▸s' • (f vv vs _)) = sym-≐ vv <≐> vs

lemma-2-wᶜ : ∀ {s₀ s' s : State} → ∀ {ef frag-w frag-rᶜ} {eflist flist-w flist-rᶜ} {prf₁ : F2L ef eflist} {prf₂ : F2L frag-w flist-w} {prf₃ : F2L frag-rᶜ flist-rᶜ}
           → {{_ : All Regular×Snapshot eflist}} → {{_ : All Regular flist-w}} → {{_ : All RecoveryCrash flist-rᶜ}}
           → s₀ ⟦ ef • f ⟧*▸ s' → s' ⟦ frag-w • wᶜ ⊙ frag-rᶜ • r ⟧*▸ s
           → State.volatile s' ≐ State.volatile s
lemma-2-wᶜ {prf₂ = prf₂} {prf₃ = prf₃} s₀▸s' (s'▸s • r sv ss _) = lemma2-2-f s₀▸s'                        <≐>
                                                                  lemma2-1 {prf₁ = prf₂} {prf₂ = prf₃} s'▸s <≐>
                                                                  sv
--
--lemma-2-fᶜ : ∀ {s₀ s₁ s₂ s : State} → ∀ {frag-w frag-rᶜ}
--           → {{_ : All Regular×Snapshot ef}} → {{_ : All Regular frag-w}} → {{_ : All RecoveryCrash frag-rᶜ}}
--           → s₀ ⟦ ef • f ⟧*▸ s₁ → s₁ ⟦ frag-w ⟧*▸ s₂ → s₂ ⟦ ([] • fᶜ) ⊙ frag-rᶜ • r ⟧*▸ s
--           → State.volatile s₂ ≐ State.volatile s ⊎ State.volatile s₁ ≐ State.volatile s
--lemma-2-fᶜ {frag-w = frag-w} {frag-rᶜ = frag-rᶜ} {{_}} {{all₁}} {{all₂}} (s₀▸s₁ • f vv vs _) s₁▸s₂ (s₂▸s • r sv ss _)
--      with splitRTC {splitOn = ([] • fᶜ)} s₂▸s
--...      | s₂' , ∅ • fᶜ (inj₁ vsᶜ) , s₂'▸s = inj₁ $ vsᶜ <≐> idemₛ (mapAll rᶜ→sp all₂ ) s₂'▸s <≐> sv
--...      | s₂' , ∅ • fᶜ (inj₂ ssᶜ) , s₂'▸s = inj₂ $ lemma2-2-f (s₀▸s₁ • f vv vs refl)    <≐>
--                                                    idemₛ (mapAll n→sp all₁) s₁▸s₂ <≐> ssᶜ <≐>
--                                                    idemₛ (mapAll rᶜ→sp all₂) s₂'▸s <≐> sv
--
--module SnapshotConsistency
--  (runSpec : (t : State) (ac : Action) → ∃[ t' ] (t ⟦ ac ⟧▸ t'))
--  (RawStateᴾ : Set) (_⟦_⟧ᴿ▸_ : RawStateᴾ → Action → RawStateᴾ → Set)
--  (RI CI : RawStateᴾ → Set)
--  (AR CR : RawStateᴾ → State → Set)
--  (Pre : RawStateᴾ → Action → Set )
--  (RIRI : {s s' : RawStateᴾ} {ac : Action} → Regular×Snapshot ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → RI s')
--  (ARAR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → Regular×Snapshot ac
--        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → AR s' t')
--  (RICI : {s s' : RawStateᴾ} {ac : Action} → RegularCrash ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → CI s')
--  (ARCR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → RegularCrash ac
--        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → CR s' t')
--  (CIRI : {s s' : RawStateᴾ} → s ⟦ r ⟧ᴿ▸ s' → CI s → RI s')
--  (CRAR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ r ⟧ᴿ▸ s' → t ⟦ r ⟧▸ t' → CI s × CR s t → AR s' t')
--  (CICI : {s s' : RawStateᴾ} → s ⟦ rᶜ ⟧ᴿ▸ s' → CI s → CI s')
--  (CRCR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ rᶜ ⟧ᴿ▸ s' → t ⟦ rᶜ ⟧▸ t' → CI s × CR s t → CR s' t')
--  (read : RawStateᴾ → Addr → Data)
--  (ObsEquiv : {s : RawStateᴾ} {t : State} → RI s × AR s t → read s ≐ State.volatile t)
--  (Init : RawStateᴾ → Set)
--  (init : {s : RawStateᴾ} → {{_ : Init s}} → ∃[ t ] (RI s × AR s t))
--  where
--
--  variable
--    rs    : RawStateᴾ
--    rs₁   : RawStateᴾ
--    rinv  : RI rs
--    cinv  : CI rs
--    rs'   : RawStateᴾ
--    rs''  : RawStateᴾ
--    rs''' : RawStateᴾ
--    rinv' : RI rs'
--    cinv' : CI rs'
--
--  _⟦_⟧ᴿ*▸_ = RTC _⟦_⟧ᴿ▸_
--
--  data Inv (rs : RawStateᴾ) : Set where
--    normal : RI rs → Inv rs
--    crash  : CI rs → Inv rs
--
--  Stateᴾ : Set
--  Stateᴾ = Σ[ rs ∈ RawStateᴾ ] Inv rs
--  unpack : Stateᴾ → RawStateᴾ
--  unpack = proj₁
--
--  variable
--    s    : Stateᴾ
--    s'   : Stateᴾ
--    s''  : Stateᴾ
--    s''' : Stateᴾ
--
--  data _⟦_⟧ᴾ▸_ : Stateᴾ → Action → Stateᴾ → Set where
--    w   : rs ⟦ w[ addr ↦ dat ] ⟧ᴿ▸ rs'  → (rs , normal rinv) ⟦ w[ addr ↦ dat ] ⟧ᴾ▸ (rs' , normal rinv')
--    wᶠ  : rs ⟦ wᶠ  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ wᶠ ⟧ᴾ▸ (rs' , normal rinv')
--    f   : rs ⟦ f   ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ f  ⟧ᴾ▸ (rs' , normal rinv')
--    wᶜ  : rs ⟦ wᶜ  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ wᶜ ⟧ᴾ▸ (rs' , crash  cinv')
--    fᶜ  : rs ⟦ fᶜ  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ fᶜ ⟧ᴾ▸ (rs' , crash  cinv')
--    rᶜ  : rs ⟦ rᶜ  ⟧ᴿ▸ rs'              → (rs , crash  cinv) ⟦ rᶜ ⟧ᴾ▸ (rs' , crash  cinv')
--    r   : rs ⟦ r   ⟧ᴿ▸ rs'              → (rs , crash  cinv) ⟦ r  ⟧ᴾ▸ (rs' , normal rinv')
--    cp  : rs ⟦ cp  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ cp ⟧ᴾ▸ (rs' , normal rinv')
--    er  : rs ⟦ er  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ er ⟧ᴾ▸ (rs' , normal rinv')
--    cpᶜ : rs ⟦ cpᶜ ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ cpᶜ ⟧ᴾ▸ (rs' , crash cinv')
--    erᶜ : rs ⟦ erᶜ ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ erᶜ ⟧ᴾ▸ (rs' , crash cinv')
--
--  _⟦_⟧ᴾ*▸_ = RTC _⟦_⟧ᴾ▸_
--
--  data SR : Stateᴾ → State → Set where
--    ar : AR rs t → SR (rs , normal rinv) t
--    cr : CR rs t → SR (rs , crash  cinv) t
--
--  simSR : SR s t → s ⟦ ac ⟧ᴾ▸ s' → ∃[ t' ] (t ⟦ ac ⟧▸ t' × SR s' t')
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (w {addr = addr} {dat = dat} rs▸rs') =
--    let (t' , t▸t') = runSpec t w[ addr ↦ dat ]
--    in   t' , t▸t' , ar (ARAR w rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (wᶠ rs▸rs') =
--    let (t' , t▸t') = runSpec t wᶠ
--    in   t' , t▸t' , ar (ARAR wᶠ rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (f rs▸rs')  =
--    let (t' , t▸t') = runSpec t f
--    in   t' , t▸t' , ar (ARAR f rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (wᶜ rs▸rs') =
--    let (t' , t▸t') = runSpec t wᶜ
--    in   t' , t▸t' , cr (ARCR wᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (fᶜ rs▸rs') =
--    let (t' , t▸t') = runSpec t fᶜ
--    in   t' , t▸t' , cr (ARCR fᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , crash  cinv} {t} (cr CR-rs-t) (rᶜ rs▸rs') =
--    let (t' , t▸t') = runSpec t rᶜ
--    in   t' , t▸t' , cr (CRCR    rs▸rs' t▸t' (cinv , CR-rs-t))
--  simSR {s , crash  cinv} {t} (cr CR-rs-t) (r rs▸rs')  =
--    let (t' , t▸t') = runSpec t r
--    in   t' , t▸t' , ar (CRAR    rs▸rs' t▸t' (cinv , CR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (cp rs▸rs')  =
--    let (t' , t▸t') = runSpec t cp
--    in   t' , t▸t' , ar (ARAR cp rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (er rs▸rs')  =
--    let (t' , t▸t') = runSpec t er
--    in   t' , t▸t' , ar (ARAR er rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (cpᶜ rs▸rs') =
--    let (t' , t▸t') = runSpec t cpᶜ
--    in   t' , t▸t' , cr (ARCR cpᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
--  simSR {s , normal rinv} {t} (ar AR-rs-t) (erᶜ rs▸rs') =
--    let (t' , t▸t') = runSpec t erᶜ
--    in   t' , t▸t' , cr (ARCR erᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
--
--  runSimSR : SR s t → s ⟦ ef ⟧ᴾ*▸ s' → ∃[ t' ] (t ⟦ ef ⟧*▸ t' × SR s' t')
--  runSimSR SR-s-t ∅                 = _ , ∅ , SR-s-t
--  runSimSR SR-s-t (s*▸s'' • s''▸s') =
--    let (t'' , t*▸t'' , SR-s''-t'') = runSimSR SR-s-t s*▸s''
--        (t'  , t''▸t' , SR-s'-t'  ) = simSR SR-s''-t'' s''▸s'
--    in  _ , (t*▸t'' • t''▸t') , SR-s'-t'
--
----original-lemma1 : Init rs → AR rs t → rs ⟦ ef ⟧ᴿ*▸ rs' → ∃[ t' ] (t ⟦ ef ⟧*▸ t')
--
--  lemma1-wᶜ : {{_ : All Regular×Snapshot ef₁}} → {{_ : All Regular ef₂}} → {{_ : All RecoveryCrash ef₃}} →
--                SR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s'' →
--                read (unpack s') ≐ read (unpack s'')
--  lemma1-wᶜ SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs') (s'*▸ • r {rinv' = rinv''} ▸rs'')
--       with runSimSR SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
--  ...     | t'  , t*▸t'   , ar AR-rs'-t'
--       with runSimSR (ar AR-rs'-t') (s'*▸ • r {rinv' = rinv''} ▸rs'')
--  ...     | t'' , t'*▸t'' , ar AR-rs''-t'' = ObsEquiv (rinv' , AR-rs'-t')            <≐>
--                                             lemma-2-wᶜ t*▸t' t'*▸t'' <≐>
--                                             sym-≐ (ObsEquiv (rinv'' , AR-rs''-t''))
--
--  lemma1-fᶜ : {{_ : All Regular×Snapshot ef₁}} → {{_ : All Regular ef₂}} → {{_ : All RecoveryCrash ef₃}} →
--                SR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ ⟧ᴾ*▸ s'' →  s'' ⟦ [] • fᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s''' →
--                read (unpack s'') ≐ read (unpack s''') ⊎ read (unpack s') ≐ read (unpack s''')
--  lemma1-fᶜ {ef₃ = ef₃}
--            SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs') rs'▸rs'' (rs''▸ • r {rinv' = rinv'''} ▸rs''')
--    with splitRTC {splitOn = [] • fᶜ} rs''▸
--  ...  | rs''₁ , ∅ • fᶜ {rinv = rinv''} rs''▸rs''₁ , rs''₁▸rs''₂
--    with runSimSR SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
--  ...  | t'   , t*▸t'     , ar AR-rs'-t'
--    with runSimSR (ar AR-rs'-t') rs'▸rs''
--  ...  | t''  , t'*▸t''   , ar AR-rs''-t''
--    with runSimSR (ar AR-rs''-t'') (rs''▸ • r {rinv' = rinv'''} ▸rs''')
--  ...  | t''' , t''*▸t''' , ar AR-rs'''-t'''
--    with lemma-2-fᶜ t*▸t' t'*▸t'' t''*▸t'''
--  ...  | inj₁ succ = inj₁ $ ObsEquiv (rinv'' , AR-rs''-t'') <≐>
--                            succ <≐> sym-≐ (ObsEquiv (rinv''' , AR-rs'''-t'''))
--  ...  | inj₂ fail = inj₂ $ ObsEquiv (rinv'  , AR-rs'-t')   <≐>
--                            fail <≐> sym-≐ (ObsEquiv (rinv''' , AR-rs'''-t'''))
--
--  initialisation : {{_ : Init rs}} → ∃[ rinv ] ∃[ t ] SR (rs , normal rinv) t
--  initialisation = let (t , RI-rs , AR-rs-t) = init
--                   in  RI-rs , t , ar AR-rs-t
--
--  lift-n×s : {{_ : All Regular×Snapshot ef}} → rs ⟦ ef ⟧ᴿ*▸ rs' →
--            ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
--  lift-n×s ∅ = _ , ∅
--  lift-n×s {{all ∷ w}} (rs*▸rs'' • rs''▸rs') =
--    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
--    in  RIRI w rs''▸rs' rinv'' , s*▸s'' • w rs''▸rs'
--  lift-n×s {{all ∷ wᶠ}} (rs*▸rs'' • rs''▸rs') =
--    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
--    in  RIRI wᶠ rs''▸rs' rinv'' , s*▸s'' • wᶠ rs''▸rs'
--  lift-n×s {{all ∷ f}} (rs*▸rs'' • rs''▸rs') =
--    let (rinv'' , s*▸s'') = lift-n×s  {{all}} rs*▸rs''
--    in  RIRI f rs''▸rs' rinv'' , s*▸s'' • f rs''▸rs'
--  lift-n×s {{all ∷ cp}} (rs*▸rs'' • rs''▸rs') =
--    let (rinv'' , s*▸s'') = lift-n×s  {{all}} rs*▸rs''
--    in  RIRI cp rs''▸rs' rinv'' , s*▸s'' • cp rs''▸rs'
--  lift-n×s {{all ∷ er}} (rs*▸rs'' • rs''▸rs') =
--    let (rinv'' , s*▸s'') = lift-n×s  {{all}} rs*▸rs''
--    in  RIRI er rs''▸rs' rinv'' , s*▸s'' • er rs''▸rs'
--
--  lift-n : {{_ : All Regular ef}} → rs ⟦ ef ⟧ᴿ*▸ rs' →
--           ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
--  lift-n {{all}} rs*▸rs' = lift-n×s {{(mapAll (λ{w → w; wᶠ → wᶠ; cp → cp; er → er}) all)}} rs*▸rs'
--
--  lift-rᶜ : {{_ : All RecoveryCrash ef}} → rs ⟦ ef ⟧ᴿ*▸ rs' →
--            ∃[ cinv' ] ((rs , crash cinv) ⟦ ef ⟧ᴾ*▸ (rs' , crash cinv'))
--  lift-rᶜ ∅ = _ , ∅
--  lift-rᶜ {{all ∷ rᶜ}} (rs*▸rs'' • rs''▸rs') =
--    let (cinv'' , s*▸s'') = lift-rᶜ {{all}} rs*▸rs''
--    in  CICI rs''▸rs' cinv'' , s*▸s'' • rᶜ rs''▸rs'
--
----  data OneRecovery : Fragment → Set where
----    or : {{_ : All Regular×Snapshot ef₁}} → {{_ : All Regular ef₂}} → {{_ : All RecoveryCrash ef₃}}
----       → OneRecovery (ef₁ • f ⊙ ef₂ • wᶜ ⊙ ef₃ • r)
----  --Behavioral Correctness on Multi-recovery Fragments.
----  BehavioralCorrectness : {{ _ : All OneRecovery ors}} → {{_ : Init rs}} → rs ⟦ ors ⊙ ef ⟧ᴿ*▸ rs' → ∃[ t ] (∃[ t' ] (t ⟦ ors ⊙ ef ⟧*▸ t' → read rs' ≐ State.volatile t'))
----  BehavioralCorrectness rstrs = let init-ri , init-t , init-ef = initialisation
----                                in   init-t , {! !} , {!!}
--
----   ef₁   f   ef₂    wᶜ    ef₃    r
---- rs   rs₁ rs'   rs'₁  rs'₂   rs'₃ rs''
--  theorem-wᶜ : {{_ : All Regular×Snapshot ef₁}} → {{_ : All Regular ef₂}} → {{_ : All RecoveryCrash ef₃}} →
--             {{_ : Init rs}} → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴿ*▸ rs'' →
--             read rs' ≐ read rs''
--  theorem-wᶜ {ef₁} {ef₂} {ef₃} {{all₁}} rs*▸rs' (rs'▸rs'₃ • r▸rs'')
--        with splitRTC {splitOn = ef₂ • wᶜ} rs'▸rs'₃
--  ...      | rs'₁ , rs'▸rs'₁ • wᶜ▸rs'₂ , rs'₁▸rs'₃ =
--               let init-ri , init-t , init-ef = initialisation
--                   wf-ri   , wf-ef            = lift-n×s {{all₁ ∷ f}} rs*▸rs'
--                   w-ri    , w-ef             = lift-n  rs'▸rs'₁
--                   rᶜ-ci   , rᶜ-ef            = lift-rᶜ rs'₁▸rs'₃
--               in  lemma1-wᶜ init-ef wf-ef
--                             (w-ef  • wᶜ {cinv' = RICI wᶜ wᶜ▸rs'₂ w-ri}  wᶜ▸rs'₂ ++RTC
--                              rᶜ-ef • r  {rinv' = CIRI    r▸rs''  rᶜ-ci} r▸rs'')
----
------   ef₁   f   ef₂    fᶜ     ef₃     r
------ rs   rs₁ rs'   rs''  rs''₁   rs''₂ rs'''
--  theorem-fᶜ : {{_ : All Regular×Snapshot ef₁}} → {{_ : All Regular ef₂}} → {{_ : All RecoveryCrash ef₃}} →
--             {{_ : Init rs}} → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ ⟧ᴿ*▸ rs'' → rs'' ⟦ ([] • fᶜ) ⊙ ef₃ • r ⟧ᴿ*▸ rs''' →
--             read rs'' ≐ read rs''' ⊎ read rs' ≐ read rs'''
--  theorem-fᶜ {ef₁} {ef₂} {ef₃} {{all₁}} rs*▸rs' rs'▸rs'' (rs''▸rs''₂ • r▸rs''')
--        with splitRTC {splitOn = [] • fᶜ} rs''▸rs''₂
--  ...      | rs''₁ , ∅ • fᶜ▸rs''₁ , rs''₁▸rs''₂
--        with let init-ri , init-t , init-ef = initialisation
--                 wf-ri   , wf-ef            = lift-n×s {{all₁ ∷ f}} rs*▸rs'
--                 w-ri    , w-ef             = lift-n  rs'▸rs''
--                 rᶜ-ci   , rᶜ-ef            = lift-rᶜ rs''₁▸rs''₂
--             in  lemma1-fᶜ init-ef wf-ef w-ef
--                           (∅     • fᶜ {cinv' = RICI fᶜ fᶜ▸rs''₁ w-ri}  fᶜ▸rs''₁ ++RTC
--                            rᶜ-ef • r  {rinv' = CIRI    r▸rs'''  rᶜ-ci} r▸rs''')
--  ...      | inj₁ succ = inj₁ succ
--  ...      | inj₂ fail = inj₂ fail
