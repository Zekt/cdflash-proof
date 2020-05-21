open import Data.Bool using (Bool; true; false)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≥_; _>_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; [_]; _∷_; _∷ʳ_; _++_)
open import Data.List.Reverse using (Reverse; reverseView)
open import Function using (_$_)

module theorem2
  (Addr : Set) (_≟_ : Addr → Addr → Bool) (_≤?MAXWCNT : Addr → Bool)
  (Data : Set) (defaultData : Data)
  where

variable
  addr : Addr
  dat  : Data


infixl 20 _•_
infixl 20 _⊙_
infixl 20 _++RTC_
infixl 20 _<≐>_
infixr 100 _[_↦_]

data SnocList (A : Set) : Set where
  []  : SnocList A
  _•_ : (as : SnocList A) → (a : A) → SnocList A

_⊙_ : {A : Set} → SnocList A → SnocList A → SnocList A
xs ⊙ []       = xs
xs ⊙ (ys • y) = (xs ⊙ ys) • y

data All {A : Set} (P : A → Set) : SnocList A → Set where
  []  : All P []
  _∷_ : ∀ {xs : SnocList A} {x : A} → All P xs → P x → All P (xs • x)

mapAll : {A : Set} {P Q : A → Set} {xs : SnocList A}
       → ({x : A} → P x → Q x) → All P xs → All Q xs
mapAll pq []        = []
mapAll pq (all ∷ x) = (mapAll pq all) ∷ (pq x)

data Action : Set where
  w[_↦_]  : (addr : Addr) (dat : Data) → Action
  f       :                              Action
  r       :                              Action
  wᶜ[_↦_] : (addr : Addr) (dat : Data) → Action
  fᶜ      :                              Action
  rᶜ      :                              Action
  cp      :                              Action
  er      :                              Action
  cpᶜ     :                              Action
  erᶜ     :                              Action

variable
  ac : Action

data Regular : Action → Set where
  w  : Regular w[ addr ↦ dat ]
  cp : Regular cp
  er : Regular er

data Write : Action → Set where
  w  : Write w[ addr ↦ dat ]

data Snapshot : Action → Set where
  f : Snapshot f

data RecoveryCrash : Action → Set where
  rᶜ : RecoveryCrash rᶜ

data RegularSuccess : Action → Set where
  w : RegularSuccess w[ addr ↦ dat ]
  f : RegularSuccess f

data Regular×Snapshot : Action → Set where
  w  : Regular×Snapshot w[ addr ↦ dat ]
  cp : Regular×Snapshot cp
  er : Regular×Snapshot er
  f  : Regular×Snapshot f

data Regular×SnapshotCrash : Action → Set where
  wᶜ  : Regular×SnapshotCrash wᶜ[ addr ↦ dat ]
  fᶜ  : Regular×SnapshotCrash fᶜ
  cpᶜ : Regular×SnapshotCrash cpᶜ
  erᶜ : Regular×SnapshotCrash erᶜ

record State : Set where
  field
    volatile : Addr → Data
    stable   : Addr → Data
    w-count  : ℕ

Init : State → Set
Init s = (addr : Addr) → (State.stable s addr ≡ defaultData)

variable
  t  : State
  t' : State

update : (Addr → Data) → Addr → Data → (Addr → Data)
update s addr dat i with addr ≤?MAXWCNT
update s addr dat i | false = s i
update s addr dat i | true with addr ≟ i
update s addr dat i | true | true  = dat
update s addr dat i | true | false = s i

_≐_ : (Addr → Data) → (Addr → Data) → Set
s ≐ t = ∀ (addr : Addr) → s addr ≡ t addr

sym-≐ : ∀ {s t : Addr → Data} → s ≐ t → t ≐ s
sym-≐ eq = λ{x → sym (eq x)}

_<≐>_ : ∀ {s t u : Addr → Data} → s ≐ t → t ≐ u → s ≐ u
_<≐>_ {s} {t} {u} e q = λ{x → begin s x ≡⟨ e x ⟩ t x ≡⟨ q x ⟩ u x ∎}

data Step (s s' : State) : Action → Set where
  w   : update (State.volatile s) addr dat ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → suc (State.w-count s) ≡ State.w-count s'
      → Step s s' w[ addr ↦ dat ]
  f   : State.volatile s ≐ State.volatile s'
      → State.volatile s ≐ State.stable s'
      → State.w-count s' ≡ zero
      → Step s s' f
  r   : State.stable s ≐ State.volatile s'
      → State.stable s ≐ State.stable s'
      → State.w-count s' ≡ zero
      → Step s s' r
  wᶜ  : State.stable s ≐ State.stable s'
      → Step s s' (wᶜ[ addr ↦ dat ])
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
  stb-w   = record { preserve = λ{(w _ ss _ ) → ss} }
  stb-wᶜ  : StbP wᶜ[ addr ↦ dat ]
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

--data Trace : Set where
--  []  :                     Trace
--  _•_ : Trace → Action → Trace
Trace = SnocList Action

--data F≅L : Trace → List Action → Set where
--  empty : F≅L [] []
--  f2l   : {x : Action} → {ef : Trace} → {la : List Action}
--        → F≅L ef la →  F≅L (ef • x) (x ∷ la)
--
--data Traces : Set where
--  []  : Traces
--  _⊡_ : Traces → Trace → Traces
Traces = SnocList Trace

--data Fs≅L : Traces → List Trace → Set where
--  empty : Fs≅L [] []
--  fs2l  : {ef : Trace} {efs : Traces} → {lf : List Trace}
--        → Fs≅L efs lf → Fs≅L (efs ⊡ ef) (ef ∷ lf)

variable
  ef  : Trace
  ef₁ : Trace
  ef₂ : Trace
  ef₃ : Trace
  frag     : Trace
  frag-w   : Trace
  frag-rᶜ  : Trace
  flist    : SnocList Action
  flist-w  : SnocList Action
  flist-rᶜ : SnocList Action



--Recursive Transitive Closure
data RTC {A S : Set} (R : S → A → S → Set) : S → SnocList A → S → Set where
  ∅   : ∀ {s : S} → RTC R s [] s
  _•_ : ∀ {s t u : S} {acs : SnocList A} {ac : A}
      → RTC R s acs t → R t ac u → RTC R s (acs • ac) u

--data RTCᶠ {S : Set} (R : S → Trace → S → Set) : S → Traces → S → Set where
--  ∅   : ∀ {s : S} → RTCᶠ R s [] s
--  _⊡_ : ∀ {s t u : S} {efs : Traces} {ef : Trace}
--      → RTCᶠ R s efs t → R t ef u → RTCᶠ R s (efs ⊡ ef) u

_⟦_⟧*▸_ = RTC  _⟦_⟧▸_
_⦅_⦆*▸_ = RTC _⟦_⟧*▸_

splitRTC : {A S : Set} {R : S → A → S → Set} {s s' : S} {splitOn rest : SnocList A}
         → RTC R s (splitOn ⊙ rest) s' → ∃[ s'' ] (RTC R s splitOn s'' × RTC R s'' rest s')
splitRTC {splitOn = ef₁} {rest = []}                t = (_ , t , ∅)
splitRTC {splitOn = ef₁} {rest = (ef₂ • ac)} (t • rr) = let (s'' , t₁ , t₂) = splitRTC t
                                                        in  (s'' , t₁ , t₂ • rr)

_++RTC_ : {A S : Set} {R : S → A → S → Set} {s t u : S} {ef₁ ef₂ : SnocList A}
        → RTC R s ef₁ t → RTC R t ef₂ u → RTC R s (ef₁ ⊙ ef₂) u
tc-s-t ++RTC ∅             = tc-s-t
tc-s-t ++RTC (tc-t-u • rr) = (tc-s-t ++RTC tc-t-u) • rr

-- split-++RTC : splitRTC (fr ++RTC fr')

idemₛ : All StbP frag
      → ∀ {s s' : State} → s ⟦ frag ⟧*▸ s'
      → State.stable s ≐ State.stable s'
idemₛ [] ∅ = λ{_ → refl}
idemₛ (all ∷ x) (s2s'' • s''2s') =
  idemₛ all s2s'' <≐> StbP.preserve x s''2s'

n→sp : Regular ac → StbP ac
n→sp w  = stb-w
n→sp cp = stb-cp
n→sp er = stb-er

rᶜ→sp : RecoveryCrash ac → StbP ac
rᶜ→sp rᶜ = stb-rᶜ

lemma2-1 : ∀ {ac : Action} → {{_ : StbP ac}}
         → {frag-w frag-rᶜ : Trace}
         → {{all₁ : All Regular frag-w}} → {{all₂ : All RecoveryCrash frag-rᶜ}}
         → ∀ {s s' : State} → s ⟦ frag-w • ac ⊙ frag-rᶜ ⟧*▸ s'
         → State.stable s ≐ State.stable s'
lemma2-1 {ac = ac} {{du}} {frag-w = frag-w} {frag-rᶜ = frag-rᶜ}
         {{all₁ = all₁}} {{all₂ = all₂}} s▸s'
    with splitRTC {splitOn = frag-w • ac} s▸s'
...    | s″ , s▸s″ • x , s″x▸s'  = idemₛ (mapAll n→sp all₁) s▸s″    <≐>
                                   StbP.preserve du x               <≐>
                                   idemₛ (mapAll rᶜ→sp all₂) s″x▸s'

lemma2-2-f : ∀ {s s' : State} {ef : Trace} → s ⟦ ef • f ⟧*▸ s' → State.volatile s' ≐ State.stable s'
lemma2-2-f (s▸s' • (f vv vs _)) = sym-≐ vv <≐> vs

lemma-2-wᶜ : ∀ {s₀ s' s : State} {ef frag-w frag-rᶜ}
           → {{_ : All Regular×Snapshot ef}} {{_ : All Regular frag-w}} {{_ : All RecoveryCrash frag-rᶜ}}
           → s₀ ⟦ ef • f ⟧*▸ s' → s' ⟦ frag-w • wᶜ[ addr ↦ dat ] ⊙ frag-rᶜ • r ⟧*▸ s
           → State.volatile s' ≐ State.volatile s
lemma-2-wᶜ s₀▸s' (s'▸s • r sv ss _) =
  lemma2-2-f s₀▸s' <≐>
  lemma2-1 s'▸s    <≐>
  sv

lemma-2-fᶜ : ∀ {s₀ s₁ s₂ s : State} {ef frag-w frag-rᶜ}
           → {{_ : All Regular×Snapshot ef}} {{_ : All Regular frag-w}} {{_ : All RecoveryCrash frag-rᶜ}}
           → s₀ ⟦ ef • f ⟧*▸ s₁ → s₁ ⟦ frag-w ⟧*▸ s₂ → s₂ ⟦ ([] • fᶜ) ⊙ frag-rᶜ • r ⟧*▸ s
           → State.volatile s₂ ≐ State.volatile s ⊎ State.volatile s₁ ≐ State.volatile s
lemma-2-fᶜ {{_}} {{all₁}} {{all₂}} (s₀▸s₁ • f vv vs _) s₁▸s₂ (s₂▸s • r sv ss _)
      with splitRTC {splitOn = ([] • fᶜ)} s₂▸s
...      | s₂' , ∅ • fᶜ (inj₁ vsᶜ) , s₂'▸s =
             inj₁ $ vsᶜ <≐> idemₛ (mapAll rᶜ→sp all₂ ) s₂'▸s <≐> sv
...      | s₂' , ∅ • fᶜ (inj₂ ssᶜ) , s₂'▸s =
             inj₂ $ lemma2-2-f (s₀▸s₁ • f vv vs refl)     <≐>
             idemₛ (mapAll n→sp all₁)  s₁▸s₂ <≐> ssᶜ <≐>
             idemₛ (mapAll rᶜ→sp all₂) s₂'▸s <≐> sv

module SnapshotConsistency
  (runSpec : (t : State) (ac : Action) → ∃[ t' ] (t ⟦ ac ⟧▸ t'))
  (RawStateᴾ : Set) (_⟦_⟧ᴿ▸_ : RawStateᴾ → Action → RawStateᴾ → Set)
  (RI CI : RawStateᴾ → Set)
  (AR CR : RawStateᴾ → State → Set)
  (Pre : RawStateᴾ → Action → Set )
  (RIRI : {s s' : RawStateᴾ} {ac : Action} → Regular×Snapshot ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → RI s')
  (ARAR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → Regular×Snapshot ac
        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → AR s' t')
  (RICI : {s s' : RawStateᴾ} {ac : Action} → Regular×SnapshotCrash ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → CI s')
  (ARCR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → Regular×SnapshotCrash ac
        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → CR s' t')
  (CIRI : {s s' : RawStateᴾ} → s ⟦ r ⟧ᴿ▸ s' → CI s → RI s')
  (CRAR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ r ⟧ᴿ▸ s' → t ⟦ r ⟧▸ t' → CI s × CR s t → AR s' t')
  (CICI : {s s' : RawStateᴾ} → s ⟦ rᶜ ⟧ᴿ▸ s' → CI s → CI s')
  (CRCR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ rᶜ ⟧ᴿ▸ s' → t ⟦ rᶜ ⟧▸ t' → CI s × CR s t → CR s' t')
  (read : RawStateᴾ → Addr → Data)
  (AR⇒ObsEquiv : {s : RawStateᴾ} {t : State} → RI s × AR s t → read s ≐ State.volatile t)
  (Initᴿ : RawStateᴾ → Set)
  (initᴿ : {s : RawStateᴾ} → {t : State} → {{_ : Initᴿ s}} → {{_ : Init t}} → (CI s × CR s t))
  where

  variable
    rs    : RawStateᴾ
    rs₁   : RawStateᴾ
    rinv  : RI rs
    cinv  : CI rs
    rs'   : RawStateᴾ
    rs''  : RawStateᴾ
    rs''' : RawStateᴾ
    rinv' : RI rs'
    cinv' : CI rs'

  _⟦_⟧ᴿ*▸_ = RTC _⟦_⟧ᴿ▸_
  _⦅_⦆ᴿ*▸_ = RTC _⟦_⟧ᴿ*▸_

  data Inv (rs : RawStateᴾ) : Set where
    normal : RI rs → Inv rs
    crash  : CI rs → Inv rs

  Stateᴾ : Set
  Stateᴾ = Σ[ rs ∈ RawStateᴾ ] Inv rs
  unpack : Stateᴾ → RawStateᴾ
  unpack = proj₁

  variable
    s    : Stateᴾ
    s'   : Stateᴾ
    s''  : Stateᴾ
    s''' : Stateᴾ

  data _⟦_⟧ᴾ▸_ : Stateᴾ → Action → Stateᴾ → Set where
    w   : rs ⟦ w[ addr ↦ dat ] ⟧ᴿ▸ rs'  → (rs , normal rinv) ⟦ w[ addr ↦ dat ] ⟧ᴾ▸ (rs' , normal rinv')
    f   : rs ⟦ f   ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ f  ⟧ᴾ▸ (rs' , normal rinv')
    wᶜ  : rs ⟦ wᶜ[ addr ↦ dat ] ⟧ᴿ▸ rs' → (rs , normal rinv) ⟦ wᶜ[ addr ↦ dat ] ⟧ᴾ▸ (rs' , crash  cinv')
    fᶜ  : rs ⟦ fᶜ  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ fᶜ ⟧ᴾ▸ (rs' , crash  cinv')
    rᶜ  : rs ⟦ rᶜ  ⟧ᴿ▸ rs'              → (rs , crash  cinv) ⟦ rᶜ ⟧ᴾ▸ (rs' , crash  cinv')
    r   : rs ⟦ r   ⟧ᴿ▸ rs'              → (rs , crash  cinv) ⟦ r  ⟧ᴾ▸ (rs' , normal rinv')
    cp  : rs ⟦ cp  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ cp ⟧ᴾ▸ (rs' , normal rinv')
    er  : rs ⟦ er  ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ er ⟧ᴾ▸ (rs' , normal rinv')
    cpᶜ : rs ⟦ cpᶜ ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ cpᶜ ⟧ᴾ▸ (rs' , crash cinv')
    erᶜ : rs ⟦ erᶜ ⟧ᴿ▸ rs'              → (rs , normal rinv) ⟦ erᶜ ⟧ᴾ▸ (rs' , crash cinv')

  data Initᴾ : Stateᴾ → Set where
    init : Initᴿ rs → Initᴾ (rs , crash cinv)

  State² = Stateᴾ × State

  Init² : State² → Set
  Init² (s , t) = Initᴾ s × Init t

  _⟦_⟧²▸_ : State² → Action → State² → Set
  (s , t) ⟦ ac ⟧²▸ (s' , t') = s ⟦ ac ⟧ᴾ▸ s' × t ⟦ ac ⟧▸ t'

  ObsEquiv : Stateᴾ → State → Set
  ObsEquiv (rs , _) t = read rs ≐ State.volatile t

  _⟦_⟧ᴾ*▸_ = RTC  _⟦_⟧ᴾ▸_
  _⦅_⦆ᴾ*▸_ = RTC _⟦_⟧ᴾ*▸_

  _⟦_⟧²*▸_ = RTC _⟦_⟧²▸_


  data SR : Stateᴾ → State → Set where
    ar : AR rs t → SR (rs , normal rinv) t
    cr : CR rs t → SR (rs , crash  cinv) t

  simSR : SR s t → s ⟦ ac ⟧ᴾ▸ s' → ∃[ t' ] (t ⟦ ac ⟧▸ t' × SR s' t')
  simSR {s , normal rinv} {t} (ar AR-rs-t) (w {addr = addr} {dat = dat} rs▸rs') =
    let (t' , t▸t') = runSpec t w[ addr ↦ dat ]
    in   t' , t▸t' , ar (ARAR w rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (f rs▸rs')  =
    let (t' , t▸t') = runSpec t f
    in   t' , t▸t' , ar (ARAR f rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (wᶜ {addr = addr} {dat = dat} rs▸rs') =
    let (t' , t▸t') = runSpec t wᶜ[ addr ↦ dat ]
    in   t' , t▸t' , cr (ARCR wᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (fᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t fᶜ
    in   t' , t▸t' , cr (ARCR fᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , crash  cinv} {t} (cr CR-rs-t) (rᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t rᶜ
    in   t' , t▸t' , cr (CRCR    rs▸rs' t▸t' (cinv , CR-rs-t))
  simSR {s , crash  cinv} {t} (cr CR-rs-t) (r rs▸rs')  =
    let (t' , t▸t') = runSpec t r
    in   t' , t▸t' , ar (CRAR    rs▸rs' t▸t' (cinv , CR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (cp rs▸rs')  =
    let (t' , t▸t') = runSpec t cp
    in   t' , t▸t' , ar (ARAR cp rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (er rs▸rs')  =
    let (t' , t▸t') = runSpec t er
    in   t' , t▸t' , ar (ARAR er rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (cpᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t cpᶜ
    in   t' , t▸t' , cr (ARCR cpᶜ rs▸rs' t▸t' (rinv , AR-rs-t))
  simSR {s , normal rinv} {t} (ar AR-rs-t) (erᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t erᶜ
    in   t' , t▸t' , cr (ARCR erᶜ rs▸rs' t▸t' (rinv , AR-rs-t))

  runSimSR : SR s t → s ⟦ ef ⟧ᴾ*▸ s' → ∃[ t' ] (t ⟦ ef ⟧*▸ t' × SR s' t')
  runSimSR SR-s-t ∅                 = _ , ∅ , SR-s-t
  runSimSR SR-s-t (s*▸s'' • s''▸s') =
    let (t'' , t*▸t'' , SR-s''-t'') = runSimSR SR-s-t s*▸s''
        (t'  , t''▸t' , SR-s'-t'  ) = simSR SR-s''-t'' s''▸s'
    in  _ , (t*▸t'' • t''▸t') , SR-s'-t'

--original-lemma1 : Init rs → AR rs t → rs ⟦ ef ⟧ᴿ*▸ rs' → ∃[ t' ] (t ⟦ ef ⟧*▸ t')

  lemma1-wᶜ : ∀ {ef₁ ef₂ ef₃ : Trace} →
              {{_ : All Regular×Snapshot ef₁}} {{_ : All Regular ef₂}} {{_ : All RecoveryCrash ef₃}} →
              SR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ • wᶜ[ addr ↦ dat ] ⊙ ef₃ • r ⟧ᴾ*▸ s'' →
              read (unpack s') ≐ read (unpack s'')
  lemma1-wᶜ SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs') (s'*▸ • r {rinv' = rinv''} ▸rs'')
       with runSimSR SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
  ...     | t'  , t*▸t'   , ar AR-rs'-t'
       with runSimSR (ar AR-rs'-t') (s'*▸ • r {rinv' = rinv''} ▸rs'')
  ...     | t'' , t'*▸t'' , ar AR-rs''-t'' =
              AR⇒ObsEquiv (rinv' , AR-rs'-t') <≐>
              lemma-2-wᶜ t*▸t' t'*▸t''        <≐>
              sym-≐ (AR⇒ObsEquiv (rinv'' , AR-rs''-t''))

  lemma1-fᶜ : ∀ {ef₁ ef₂ ef₃ : Trace}
                {{_ : All Regular×Snapshot ef₁}} {{_ : All Regular ef₂}} {{_ : All RecoveryCrash ef₃}} →
              SR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ ⟧ᴾ*▸ s'' →  s'' ⟦ [] • fᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s''' →
              read (unpack s'') ≐ read (unpack s''') ⊎ read (unpack s') ≐ read (unpack s''')
  lemma1-fᶜ {ef₃ = ef₃} SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs') rs'▸rs'' (rs''▸ • r {rinv' = rinv'''} ▸rs''')
    with splitRTC {splitOn = [] • fᶜ} rs''▸
  ...  | rs''₁ , ∅ • fᶜ {rinv = rinv''} rs''▸rs''₁ , rs''₁▸rs''₂
    with runSimSR SR-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
  ...  | t'   , t*▸t'     , ar AR-rs'-t'
    with runSimSR (ar AR-rs'-t') rs'▸rs''
  ...  | t''  , t'*▸t''   , ar AR-rs''-t''
    with runSimSR (ar AR-rs''-t'') (rs''▸ • r {rinv' = rinv'''} ▸rs''')
  ...  | t''' , t''*▸t''' , ar AR-rs'''-t'''
    with lemma-2-fᶜ t*▸t' t'*▸t'' t''*▸t'''
  ...  | inj₁ succ = inj₁ $ AR⇒ObsEquiv (rinv'' , AR-rs''-t'') <≐>
                            succ <≐> sym-≐ (AR⇒ObsEquiv (rinv''' , AR-rs'''-t'''))
  ...  | inj₂ fail = inj₂ $ AR⇒ObsEquiv (rinv'  , AR-rs'-t')   <≐>
                            fail <≐> sym-≐ (AR⇒ObsEquiv (rinv''' , AR-rs'''-t'''))

----  initialisation : {{_ : Initᴾ rs}} → ∃[ rinv ] ∃[ t ] SR (rs , normal rinv) t
----  initialisation = let (t , RI-rs , AR-rs-t) = initᴾ
----                   in  RI-rs , t , ar AR-rs-t
--
  lift-n×s : ∀ {ef : Trace} {{_ : All Regular×Snapshot ef}} → rs ⟦ ef ⟧ᴿ*▸ rs' →
             ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
  lift-n×s ∅ = _ , ∅
  lift-n×s {{all ∷ w}} (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
    in  RIRI w rs''▸rs' rinv'' , s*▸s'' • w rs''▸rs'
  lift-n×s {{all ∷ f}} (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
    in  RIRI f rs''▸rs' rinv'' , s*▸s'' • f rs''▸rs'
  lift-n×s {{all ∷ cp}} (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
    in  RIRI cp rs''▸rs' rinv'' , s*▸s'' • cp rs''▸rs'
  lift-n×s {{all ∷ er}} (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-n×s {{all}} rs*▸rs''
    in  RIRI er rs''▸rs' rinv'' , s*▸s'' • er rs''▸rs'

  lift-n : ∀ {ef : Trace} {{_ : All Regular ef}} → rs ⟦ ef ⟧ᴿ*▸ rs'
         → ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
  lift-n {{all}} rs*▸rs' =
    lift-n×s {{(mapAll (λ{w → w; cp → cp; er → er}) all)}} rs*▸rs'

  lift-rᶜ : ∀ {ef : Trace} {{_ : All RecoveryCrash ef}} → rs ⟦ ef ⟧ᴿ*▸ rs' →
            ∃[ cinv' ] ((rs , crash cinv) ⟦ ef ⟧ᴾ*▸ (rs' , crash cinv'))
  lift-rᶜ ∅ = _ , ∅
  lift-rᶜ {{all ∷ rᶜ}} (rs*▸rs'' • rs''▸rs') =
    let (cinv'' , s*▸s'') = lift-rᶜ {{all}} rs*▸rs''
    in  CICI rs''▸rs' cinv'' , s*▸s'' • rᶜ rs''▸rs'

  data OneRecovery : Trace → Set where
    wᶜ     : {tr₁ tr₂ tr₃ : Trace} → All Regular×Snapshot tr₁ → All Regular tr₂ → All RecoveryCrash tr₃
           → OneRecovery (tr₁ ⊙ ([] • f ⊙ tr₂) ⊙ ([] • wᶜ[ addr ↦ dat ] ⊙ tr₃ • r))
--  fᶜ     : ∀ {s₁ s₂ s₃ s₄ : S} {tr₁ tr₂ tr₃ : Trace}
--         → All Regular×Snapshot tr₁ → All Regular tr₂ → All RecoveryCrash tr₃
--         → (fr₁ : RTC R s₁ tr₁ s₂) → (fr₂ : RTC R s₂ ([] • f ⊙ tr₂) s₃) (fr₃ : RTC R s₃ ([] • fᶜ ⊙ tr₃ • r) s₄)
--         → OneRecovery (fr₁ ++RTC fr₂ ++RTC fr₃)
--  wᶜ-nof : ∀ {s₂ s₃ s₄ : S} {tr₂ tr₃ : Trace}
--         → All Regular tr₂ → All RecoveryCrash tr₃
--         → (fr₂ : RTC R s₂ tr₂ s₃) (fr₃ : RTC R s₃ ([] • wᶜ[ addr ↦ dat ] ⊙ tr₃ • r) s₄)
--         → OneRecovery (fr₂ ++RTC fr₃)
--  fᶜ-nof : ∀ {s₂ s₃ s₄ : S} {tr₂ tr₃ : Trace}
--         → All Regular tr₂ → All RecoveryCrash tr₃
--         → (fr₂ : RTC R s₂ tr₂ s₃) → (fr₃ : RTC R s₃ (([] • fᶜ) ⊙ tr₃ • r) s₄)
--         → OneRecovery (fr₂ ++RTC fr₃)

--   data OneRecovery {S : Set}  {R : S → Action → S → Set} : {s s' : S} {tr : Trace} → RTC R s tr s' → Set where
--     wᶜ     : ∀ {s₁ s₂ s₃ s₄ : S} {tr₁ tr₂ tr₃ : Trace}
--            → All Regular×Snapshot tr₁ → All Regular tr₂ → All RecoveryCrash tr₃
--            → (fr₁ : RTC R s₁ tr₁ s₂) → (fr₂ : RTC R s₂ ([] • f ⊙ tr₂) s₃) → (fr₃ : RTC R s₃ ([] • wᶜ[ addr ↦ dat ] ⊙ tr₃ • r) s₄)
--            → OneRecovery (fr₁ ++RTC fr₂ ++RTC fr₃)
--     fᶜ     : ∀ {s₁ s₂ s₃ s₄ : S} {tr₁ tr₂ tr₃ : Trace}
--            → All Regular×Snapshot tr₁ → All Regular tr₂ → All RecoveryCrash tr₃
--            → (fr₁ : RTC R s₁ tr₁ s₂) → (fr₂ : RTC R s₂ ([] • f ⊙ tr₂) s₃) (fr₃ : RTC R s₃ ([] • fᶜ ⊙ tr₃ • r) s₄)
--            → OneRecovery (fr₁ ++RTC fr₂ ++RTC fr₃)
--     wᶜ-nof : ∀ {s₂ s₃ s₄ : S} {tr₂ tr₃ : Trace}
--            → All Regular tr₂ → All RecoveryCrash tr₃
--            → (fr₂ : RTC R s₂ tr₂ s₃) (fr₃ : RTC R s₃ ([] • wᶜ[ addr ↦ dat ] ⊙ tr₃ • r) s₄)
--            → OneRecovery (fr₂ ++RTC fr₃)
--     fᶜ-nof : ∀ {s₂ s₃ s₄ : S} {tr₂ tr₃ : Trace}
--            → All Regular tr₂ → All RecoveryCrash tr₃
--            → (fr₂ : RTC R s₂ tr₂ s₃) → (fr₃ : RTC R s₃ (([] • fᶜ) ⊙ tr₃ • r) s₄)
--            → OneRecovery (fr₂ ++RTC fr₃)

  data MultiRecovery : Trace → Set where
    init : {tr : Trace} → All RecoveryCrash tr → MultiRecovery (tr • r)
    one  : {tr₁ tr₂ : Trace} → MultiRecovery tr₁ → OneRecovery tr₂ → MultiRecovery (tr₁ ⊙ tr₂)
    zero : {tr₁ tr₂ : Trace} → MultiRecovery tr₁ → All Regular×Snapshot tr₂ → MultiRecovery (tr₁ ⊙ tr₂)

--   data MultiRecovery {S : Set}  {R : S → Action → S → Set} : {s s' : S} {tr : Trace} → RTC R s tr s' → Set where
--     init : ∀ {s₁ s₂ tr} → (All RecoveryCrash tr) → {fr : RTC R s₁ (tr • r) s₂} → MultiRecovery fr
--     one  : ∀ {s₁ s₂ s₃ : S} {tr₁ tr₂ : Trace} {fr₁ : RTC R s₁ tr₁ s₂} {fr₂ : RTC R s₂ tr₂ s₃}
--          → MultiRecovery fr₁ → OneRecovery fr₂ → MultiRecovery (fr₁ ++RTC fr₂)
--     zero : ∀ {s₁ s₂ s₃ : S} {tr₁ tr₂ : Trace} → All Regular×Snapshot tr₂ → {fr₁ : RTC R s₁ tr₁ s₂} {fr₂ : RTC R s₂ tr₂ s₃}
--          → MultiRecovery fr₁ → MultiRecovery (fr₁ ++RTC fr₂)

--   --Behavioral Correctness on Multi-recovery Traces.

--   GBC-ARS : {S : Set} (Pred : S → Set) {R : S → Action → S → Set} {p p' : S} {tr : Trace}
--           → (fr : RTC R p tr p') → Set
--   GBC-ARS pred {p' = p'} ∅ = pred p'
--   GBC-ARS pred {p' = p'} (fr • _) = GBC-ARS pred fr × (pred p')

--   GBC-OR : {S : Set} (Pred : S → Set) {R : S → Action → S → Set} {p : S} (p' : S) {tr : Trace}
--          → {fr : RTC R p tr p'} → OneRecovery fr → Set
--   GBC-OR pred p' (wᶜ _ _ _ fr₁ fr₂ fr₃) = GBC-ARS pred fr₁ × GBC-ARS pred fr₂ × pred p'
--   GBC-OR pred p' (fᶜ _ _ _ fr₁ fr₂ fr₃) = GBC-ARS pred fr₁ × GBC-ARS pred fr₂ × pred p'
--   GBC-OR pred p' (wᶜ-nof _ _ fr₂ fr₃) = GBC-ARS pred fr₂ × pred p'
--   GBC-OR pred p' (fᶜ-nof _ _ fr₂ fr₃) = GBC-ARS pred fr₂ × pred p'

--   GBC : {S : Set} (Pred : S → Set) {R : S → Action → S → Set} {p p' : S} {tr : Trace} (Init : S → Set) → Init p
--       → {fr : RTC R p tr p'} → MultiRecovery fr → Set
--   GBC pred {p' = p'} Init initp (init _) = pred p'
--   GBC pred {p' = p'} Init initp (one mr or) = GBC pred Init initp mr × GBC-OR pred p' or
--   GBC pred {p' = p'} Init initp (zero all {fr₂ = fr₂} mr) = GBC pred Init initp mr × GBC-ARS pred fr₂

  Conformance-all : {tr : Trace} {s s' : Stateᴾ} → s ⟦ tr ⟧ᴾ*▸ s' → {t t' : State} → t ⟦ tr ⟧*▸ t' → Set
  Conformance-all {s' = s'} ∅         {t' = t'} ∅         = ⊤
  Conformance-all {s' = s'} (frP • _) {t' = t'} (frS • _) = Conformance-all frP frS × ObsEquiv s' t'

  data 1RFrags {S : Set} {R : S → Action → S → Set} : {s s' : S} {tr : Trace} → OneRecovery tr → RTC R s tr s' → Set where
    wᶜ : {tr₁ tr₂ tr₃ : Trace} {all₁ : All Regular×Snapshot tr₁} {all₂ : All Regular tr₂} {all₃ : All RecoveryCrash tr₃}
       → {s₁ s₂ s₃ s₄ : S} (fr₁ : RTC R s₁ tr₁ s₂) (fr₂ : RTC R s₂ ([] • f ⊙ tr₂) s₃) (fr₃ : RTC R s₃ ([] • wᶜ[ addr ↦ dat ] ⊙ tr₃ • r) s₄)
       → 1RFrags (wᶜ all₁ all₂ all₃) (fr₁ ++RTC fr₂ ++RTC fr₃)

  view1R : {tr : Trace} (1r : OneRecovery tr) {S : Set} {R : S → Action → S → Set} {s s' : S} (fr : RTC R s tr s') → 1RFrags 1r fr
  view1R = {!!}

  Conformance-1R : {tr : Trace} (1r : OneRecovery tr)
                 → {s s' : Stateᴾ} (frP : s ⟦ tr ⟧ᴾ*▸ s') → 1RFrags 1r frP
                 → {t t' : State } (frS : t ⟦ tr ⟧*▸  t') → 1RFrags 1r frS → Set
  Conformance-1R (wᶜ {tr₁ = tr₁} {tr₂} {tr₃} _ _ _)
    {s' = s'} .(frP₁ ++RTC frP₂ ++RTC frP₃) (wᶜ frP₁ frP₂ frP₃) {t' = t'} .(frS₁ ++RTC frS₂ ++RTC frS₃) (wᶜ frS₁ frS₂ frS₃) =
    Conformance-all (frP₁ ++RTC frP₂) (frS₁ ++RTC frS₂) × ObsEquiv s' t'

  data MRFrags {S : Set} {R : S → Action → S → Set} : {s s' : S} {tr : Trace} → MultiRecovery tr → RTC R s tr s' → Set where
    init : {tr : Trace} {all : All RecoveryCrash tr} {s s' : S} (fr : RTC R s (tr • r) s') → MRFrags (init all) fr
    one  : {tr₁ : Trace} {mr : MultiRecovery tr₁} {s₁ s₂ : S} {fr₁ : RTC R s₁ tr₁ s₂} → MRFrags mr fr₁
         → {tr₂ : Trace} {1r : OneRecovery   tr₂} {s₃    : S} (fr₂ : RTC R s₂ tr₂ s₃) → MRFrags (one mr 1r) (fr₁ ++RTC fr₂)
    zero : {tr₁ : Trace} {mr : MultiRecovery tr₁} {s₁ s₂ : S} {fr₁ : RTC R s₁ tr₁ s₂} → MRFrags mr fr₁
         → {tr₂ : Trace} {all : All Regular×Snapshot tr₂} {s₃ : S} (fr₂ : RTC R s₂ tr₂ s₃) → MRFrags (zero mr all) (fr₁ ++RTC fr₂)

  viewMR : {tr : Trace} (mr : MultiRecovery tr) {S : Set} {R : S → Action → S → Set} {s s' : S} (fr : RTC R s tr s') → MRFrags mr fr
  viewMR = {!!}

  Conformance : {tr : Trace} (mr : MultiRecovery tr)
                {s s' : Stateᴾ} (frP : s ⟦ tr ⟧ᴾ*▸ s') → MRFrags mr frP
              → {t t' : State } (frS : t ⟦ tr ⟧*▸  t') → MRFrags mr frS → Set
  Conformance (init _) {s' = s'} _ _ {t' = t'} _ _ = ObsEquiv s' t'
  Conformance (one mr 1r) .(_ ++RTC frP₂) (one {s₂ = s''} frPs frP₂) .(_ ++RTC frS₂) (one {s₂ = t''} frSs frS₂) =
    Conformance mr _ frPs _ frSs × ObsEquiv s'' t'' × Conformance-1R 1r frP₂ (view1R 1r frP₂) frS₂ (view1R 1r frS₂)
  Conformance (zero mr _) .(_ ++RTC frP₂) (zero {s₂ = s''} frPs frP₂) .(_ ++RTC frS₂) (zero {s₂ = t''} frSs frS₂) =
    Conformance mr _ frPs _ frSs × ObsEquiv s'' t'' × Conformance-all frP₂ frS₂

  BC-all : {tr : Trace} → All Regular×Snapshot tr → {s s' : Stateᴾ} {t : State} →
           SR s t → (frP : s ⟦ tr ⟧ᴾ*▸ s') → Σ[ t' ∈ State ] Σ[ frS ∈ t ⟦ tr ⟧*▸ t' ] SR s' t' × ObsEquiv s' t' × Conformance-all frP frS
  BC-all [] sr ∅ = _ , ∅ , sr , {!!} , tt
  BC-all (all ∷ _) sr (frP • x₁) with BC-all all sr frP
  BC-all (all ∷ _) sr (frP • s''▸s') | t'' , frS'' , sr'' , oe'' , conf'' with simSR sr'' s''▸s'
  BC-all (all ∷ w) sr (frP • w {rinv' = rinv'} rs''▸s') | t'' , frS'' , sr'' , oe'' , conf'' | t' , t''▸t' , ar ar' =
    let oe' = AR⇒ObsEquiv (rinv' , ar') in t' , frS'' • t''▸t' , ar ar' , oe' , conf'' , oe'
  BC-all (all ∷ cp) sr (frP • cp rs''▸s') | t'' , frS'' , sr'' , oe'' , conf'' | t' , t''▸t' , ar ar' = {!!}
  BC-all (all ∷ er) sr (frP • er rs''▸s') | t'' , frS'' , sr'' , oe'' , conf'' | t' , t''▸t' , ar ar' = {!!}
  BC-all (all ∷ f) sr (frP • f rs''▸s') | t'' , frS'' , sr'' , oe'' , conf'' | t' , t''▸t' , ar ar' = {!!}

  BC : {tr : Trace} (mr : MultiRecovery tr) {s s' : Stateᴾ} → Initᴾ s → (frP : s ⟦ tr ⟧ᴾ*▸ s') (frPs : MRFrags mr frP)
     → Σ[ t ∈ State ] Init t × Σ[ t' ∈ State ] SR s' t' × ObsEquiv s' t' × Σ[ frS ∈ t ⟦ tr ⟧*▸ t' ] Σ[ frSs ∈ MRFrags mr frS ] Conformance mr frP frPs frS frSs
  BC (init x) init-s frP frPs = {!!}
  BC (one mr x) init-s frP frPs = {!!}
  BC (zero {tr₁ = tr₁} mr all) init-s .(_ ++RTC frP₂) (zero frPs frP₂) with BC mr init-s _ frPs
  ... | t , init-t , t'' , sr'' , oe'' , frS₁ , frSs₁ , conf₁ with BC-all all sr'' frP₂
  ... | t' , frS₂ , sr' , oe' , conf₂ = t , init-t , t' , sr' , oe' , frS₁ ++RTC frS₂ , zero frSs₁ frS₂ , conf₁ , oe'' , conf₂

  BehavioralCorrectness :
    {tr : Trace} (mr : MultiRecovery tr) {s s' : Stateᴾ} → Initᴾ s → (frP : s ⟦ tr ⟧ᴾ*▸ s') →
    Σ[ t ∈ State ] Init t × Σ[ t' ∈ State ] Σ[ frS ∈ t ⟦ tr ⟧*▸ t' ] Σ[ frPs ∈ MRFrags mr frP ] Σ[ frSs ∈ MRFrags mr frS ] Conformance mr frP frPs frS frSs
  BehavioralCorrectness mr init-s frP =
    let frPs = viewMR mr frP
        (t , init-t , t' , _ , _ , frS , frSs , conf) = BC mr init-s frP frPs
    in  t , init-t , t' , frS , frPs , frSs , conf

--   --  bc : Initᴾ rs → Init t
--   --     → rs ⟦ efs • (ef • ac) ⦆ᴿ*▸ rs' → t ⦅ efs • (ef • ac) ⦆*▸ t
--   --     → (Regular×Snapshot ac → read rs' ≐ State.volatile t') × BC (efs • ef) → BC (efs • (ef • ac))

--   --BehavioralCorrectness : ∀ {efs : Traces} {ef : Trace} {efslist : List Trace} {eflist : List Action}
--   --                          {prf₁ : Fs≅L efs efslist}       {prf₂ : F≅L ef eflist}
--   --                          {{_ : All OneRecovery efslist}} {{_ : All Regular×Snapshot eflist}}
--   --                        → (_ : Init rs) → rs ⦅ efs ⊡ ef ⦆ᴿ*▸ rs'
--   --                        → ∃[ t ] (∃[ t' ] (t ⦅ efs ⊡ ef ⦆*▸ t' × read rs' ≐ State.volatile t'))
--   --BehavioralCorrectness (rs▸ ⊡ ∅) = {!   !}
--   --BehavioralCorrectness {prf₂ = f2l prf₂} {{all₁}} {{all₂ ∷ rsx}} (rs▸ ⊡ (▸rs' • step)) = {!   !}
--   --BehavioralCorrectness {prf₂ = prf₂} (rs▸ ⊡ ▸rs') = let init-ri , init-t , init-ef = initialisation
--   --                                                       rinv'   , smt              = lift-n×s {prf = prf₂} ▸rs'
--   --                                                   in  init-t , {!   !} , λ{ x → ObsEquiv {!   !} }

-- --   ef₁   f   ef₂    wᶜ    ef₃    r
-- -- rs   rs₁ rs'   rs'₁  rs'₂   rs'₃ rs''
-- --  theorem-wᶜ : ∀ {ef₁ ef₂ ef₃ : Trace} {eflist flist-w flist-rᶜ : List Action} →
-- --               {prf₁ : F≅L ef₁ eflist} {prf₂ : F≅L ef₂ flist-w} {prf₃ : F≅L ef₃ flist-rᶜ}
-- --               {{_ : All Regular×Snapshot eflist}} {{_ : All Regular flist-w}} {{_ : All RecoveryCrash flist-rᶜ}} →
-- --               {{_ : Initᴾ rs}} → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴿ*▸ rs'' →
-- --               read rs' ≐ read rs''
-- --  theorem-wᶜ {ef₁ = ef₁} {ef₂ = ef₂} {ef₃ = ef₃} {prf₁ = prf₁} {prf₂ = prf₂} {prf₃ = prf₃}
-- --             {{all₁}} rs*▸rs' (rs'▸rs'₃ • r▸rs'')
-- --        with splitRTC {splitOn = ef₂ • wᶜ} rs'▸rs'₃
-- --  ...      | rs'₁ , rs'▸rs'₁ • wᶜ▸rs'₂ , rs'₁▸rs'₃ =
-- --               let init-ri , init-t , init-ef = initialisation
-- --                   wf-ri   , wf-ef            = lift-n×s {prf = f2l prf₁} {{all₁ ∷ f}} rs*▸rs'
-- --                   w-ri    , w-ef             = lift-n   {prf = prf₂} rs'▸rs'₁
-- --                   rᶜ-ci   , rᶜ-ef            = lift-rᶜ  {prf = prf₃} rs'₁▸rs'₃
-- --               in  lemma1-wᶜ {prf₁ = prf₁} {prf₂ = prf₂} {prf₃ = prf₃} init-ef wf-ef
-- --                             (w-ef  • wᶜ {cinv' = RICI wᶜ wᶜ▸rs'₂ w-ri}  wᶜ▸rs'₂ ++RTC
-- --                              rᶜ-ef • r  {rinv' = CIRI    r▸rs''  rᶜ-ci} r▸rs'')
-- ----
-- ------   ef₁   f   ef₂    fᶜ     ef₃     r
-- ------ rs   rs₁ rs'   rs''  rs''₁   rs''₂ rs'''
-- --  theorem-fᶜ : ∀ {ef₁ ef₂ ef₃ : Trace} {eflist flist-w flist-rᶜ : List Action} →
-- --               {prf₁ : F≅L ef₁ eflist} {prf₂ : F≅L ef₂ flist-w} {prf₃ : F≅L ef₃ flist-rᶜ}
-- --               {{_ : All Regular×Snapshot eflist}} {{_ : All Regular flist-w}} {{_ : All RecoveryCrash flist-rᶜ}} →
-- --               {{_ : Initᴾ rs}} → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ ⟧ᴿ*▸ rs'' → rs'' ⟦ ([] • fᶜ) ⊙ ef₃ • r ⟧ᴿ*▸ rs''' →
-- --               read rs'' ≐ read rs''' ⊎ read rs' ≐ read rs'''
-- --  theorem-fᶜ {ef₁} {ef₂} {ef₃} {prf₁ = prf₁} {prf₂ = prf₂} {prf₃ = prf₃}
-- --             {{all₁}} rs*▸rs' rs'▸rs'' (rs''▸rs''₂ • r▸rs''')
-- --        with splitRTC {splitOn = [] • fᶜ} rs''▸rs''₂
-- --  ...      | rs''₁ , ∅ • fᶜ▸rs''₁ , rs''₁▸rs''₂
-- --        with let init-ri , init-t , init-ef = initialisation
-- --                 wf-ri   , wf-ef            = lift-n×s {prf = f2l prf₁} {{all₁ ∷ f}} rs*▸rs'
-- --                 w-ri    , w-ef             = lift-n  {prf = prf₂} rs'▸rs''
-- --                 rᶜ-ci   , rᶜ-ef            = lift-rᶜ {prf = prf₃} rs''₁▸rs''₂
-- --             in  lemma1-fᶜ {prf₁ = prf₁} {prf₂ = prf₂} {prf₃ = prf₃} init-ef wf-ef w-ef
-- --                           (∅     • fᶜ {cinv' = RICI fᶜ fᶜ▸rs''₁ w-ri}  fᶜ▸rs''₁ ++RTC
-- --                            rᶜ-ef • r  {rinv' = CIRI    r▸rs'''  rᶜ-ci} r▸rs''')
-- --  ...      | inj₁ succ = inj₁ succ
-- --  ...      | inj₂ fail = inj₂ fail
