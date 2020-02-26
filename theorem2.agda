open import Data.Bool

module theorem2 (Addr : Set) (_≟_ : Addr → Addr → Bool) (Data : Set) where

variable
  addr : Addr
  dat  : Data

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃; ∃-syntax; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec
open import Function using (_$_; _∘_)

infixl 20 _•_
infixl 20 _⊙_
infixl 20 _++RTC_
infixl 20 _>≐>_
infixr 100 _[_↦_]

data Action : Set where
  w[_↦_] : (addr : Addr) (dat : Data) → Action
  f      :                              Action
  r      :                              Action
  wᶜ     :                              Action
  fᶜ     :                              Action
  rᶜ     :                              Action

variable
  ac : Action

-- Stable Reserving Actions
data isSR : Action → Set where -- disjoint union of stable reserving actions
  w  : isSR w[ addr ↦ dat ]
  r  : isSR r
  wᶜ : isSR wᶜ
  rᶜ : isSR rᶜ

data Success : Action → Set where -- disjoint union of success functions
  w : ac ≡ w[ addr ↦ dat ] → Success w[ addr ↦ dat ]
  f : ac ≡ f → Success f
  r : ac ≡ r → Success r

data Crash : Action → Set where -- disjoint union of crash functions
  wᶜ : ac ≡ wᶜ → Crash wᶜ
  fᶜ : ac ≡ fᶜ → Crash fᶜ
  rᶜ : ac ≡ rᶜ → Crash rᶜ

data Crash* : Action → Set where -- disjoint union of crash functions we care
  wᶜ : ac ≡ wᶜ → Crash* wᶜ
  fᶜ : ac ≡ fᶜ → Crash* fᶜ

data Write : Action → Set where
  w : Write w[ addr ↦ dat ]

data RecoveryCrash : Action → Set where
  rᶜ : RecoveryCrash rᶜ

data NormalSuccess : Action → Set where
  w : NormalSuccess w[ addr ↦ dat ]
  f : NormalSuccess f

data NormalCrash : Action → Set where
  wᶜ : NormalCrash wᶜ
  fᶜ : NormalCrash fᶜ
record State : Set where
  constructor <_,_>
  field
    volatile : Addr → Data
    stable   : Addr → Data

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

_>≐>_ : ∀ {s t u : Addr → Data} → s ≐ t → t ≐ u → s ≐ u
_>≐>_ {s} {t} {u} e q = λ{x → begin s x ≡⟨ e x ⟩ t x ≡⟨ q x ⟩ u x ∎}

data Step (s s' : State) : Action → Set where
  w  : (addr : Addr) (dat : Data) → State.volatile s [ addr ↦ dat ] ≐ State.volatile s'
                                          → State.stable s ≐ State.stable s'
                                          → Step s s' w[ addr ↦ dat ]
  f  : State.volatile s ≐ State.volatile s'
     → State.volatile s ≐ State.stable s'
     → Step s s' f
  r  : State.stable s ≐ State.volatile s'
     → State.stable s ≐ State.stable s'
     → Step s s' r
  wᶜ : State.stable s ≐ State.stable s'
     → Step s s' wᶜ
  fᶜ : State.volatile s ≐ State.stable s' ⊎ State.stable s ≐ State.stable s'
     → Step s s' fᶜ
  rᶜ : State.stable s ≐ State.stable s'
     → Step s s' rᶜ

_⟦_⟧▸_ : State → Action → State → Set
s ⟦ ac ⟧▸ s' = Step s s' ac

data Fragment : Set where
  []  : Fragment
  _•_ : Fragment → Action → Fragment

variable
  ef  : Fragment
  ef₁ : Fragment
  ef₂ : Fragment
  ef₃ : Fragment

data All (P : Action → Set) : Fragment → Set where
  []  : All P []
  _∷_ : ∀ {x : Action} {xs : Fragment} → All P xs → P x → All P (xs • x)

mapAll : {P Q : Action → Set} {xs : Fragment} → ({x : Action} → P x → Q x) → All P xs → All Q xs
mapAll pq []        = []
mapAll pq (all ∷ x) = mapAll pq all ∷ pq x

_⊙_ : Fragment → Fragment → Fragment
xs ⊙ []       = xs
xs ⊙ (ys • y) = (xs ⊙ ys) • y

data RTC {S : Set} (R : S → Action → S → Set) : S → Fragment → S → Set where
  ∅   : ∀ {s : S} → RTC R s [] s
  _•_ : ∀ {s t u : S} {acs : Fragment} {ac : Action}
      → RTC R s acs t → R t ac u → RTC R s (acs • ac) u

_⟦_⟧*▸_ = RTC _⟦_⟧▸_

splitRTC : {S : Set} {R : S → Action → S → Set} {s s' : S} (ef₁ ef₂ : Fragment)
         → RTC R s (ef₁ ⊙ ef₂) s' → ∃[ s'' ] (RTC R s ef₁ s'' × RTC R s'' ef₂ s')
splitRTC ef₁ []                t = (_ , t , ∅)
splitRTC ef₁ (ef₂ • ac) (t • rr) = let (s'' , t₁ , t₂) = splitRTC ef₁ ef₂ t in (s'' , t₁ , t₂ • rr)

_++RTC_ : {S : Set} {R : S → Action → S → Set} {s t u : S} {ef₁ ef₂ : Fragment}
        → RTC R s ef₁ t → RTC R t ef₂ u → RTC R s (ef₁ ⊙ ef₂) u
tc-s-t ++RTC ∅             = tc-s-t
tc-s-t ++RTC (tc-t-u • rr) = (tc-s-t ++RTC tc-t-u) • rr

reserve : {ac : Action} → isSR ac → {s s' : State} → s ⟦ ac ⟧▸ s' → (State.stable s ≐ State.stable s')
reserve w  (w _ _ _ ss) = ss
reserve r  (r _ ss)     = ss
reserve wᶜ (wᶜ ss)      = ss
reserve rᶜ (rᶜ ss)      = ss

idemₛ : ∀ {frag : Fragment} → All isSR frag
      → ∀ {s s' : State} → s ⟦ frag ⟧*▸ s'
      → State.stable s ≐ State.stable s'
idemₛ [] ∅ = λ{_ → refl}
idemₛ (all ∷ x) (s*▸s'' • s''▸s') = (idemₛ all s*▸s'') >≐> reserve x s''▸s'

w→sr : Write ac → isSR ac
w→sr w = w

rᶜ→sr : RecoveryCrash ac → isSR ac
rᶜ→sr rᶜ = rᶜ

lemma2-1 : ∀ {ac : Action} → isSR ac
         → ∀ {frag-w frag-rᶜ : Fragment}
         → All Write frag-w → All RecoveryCrash frag-rᶜ
         → ∀ {s s' : State} → s ⟦ frag-w • ac ⊙ frag-rᶜ ⟧*▸ s'
         → State.stable s ≐ State.stable s'
lemma2-1 {ac} du {frag-w} {frag-rᶜ} all₁ all₂ s▸s' with splitRTC (frag-w • ac) frag-rᶜ s▸s'
...    | s″ , s▸s″ • x , s″x▸s'  = idemₛ (mapAll w→sr all₁) s▸s″    >≐>
                                   reserve du x                     >≐>
                                   idemₛ (mapAll rᶜ→sr all₂) s″x▸s'

lemma2-2-f : ∀ {s s' : State} {ef : Fragment} → s ⟦ ef • f ⟧*▸ s' → State.volatile s' ≐ State.stable s'
lemma2-2-f (s▸s' • (f vv vs)) = sym-≐ vv >≐> vs

lemma-2-wᶜ : ∀ {s₀ s' s : State} → ∀ {ef frag-w frag-rᶜ}
           → All NormalSuccess ef → All Write frag-w → All RecoveryCrash frag-rᶜ
           → s₀ ⟦ ef • f ⟧*▸ s' → s' ⟦ frag-w • wᶜ ⊙ frag-rᶜ • r ⟧*▸ s
           → State.volatile s' ≐ State.volatile s
lemma-2-wᶜ _ all₁ all₂ s₀▸s' (s'▸s • r sv ss) = lemma2-2-f s₀▸s'           >≐>
                                                lemma2-1 wᶜ all₁ all₂ s'▸s >≐>
                                                sv

lemma-2-fᶜ : ∀ {s₀ s₁ s₂ s : State} → ∀ {frag-w frag-rᶜ}
           → All NormalSuccess ef → All Write frag-w → All RecoveryCrash frag-rᶜ
           → s₀ ⟦ ef • f ⟧*▸ s₁ → s₁ ⟦ frag-w ⟧*▸ s₂ → s₂ ⟦ ([] • fᶜ) ⊙ frag-rᶜ • r ⟧*▸ s
           → State.volatile s₂ ≐ State.volatile s ⊎ State.volatile s₁ ≐ State.volatile s
lemma-2-fᶜ {frag-w = frag-w} {frag-rᶜ = frag-rᶜ} _ all₁ all₂ (s₀▸s₁ • f vv vs) s₁▸s₂ (s₂▸s • r sv ss)
      with splitRTC ([] • fᶜ) frag-rᶜ s₂▸s
...      | s₂' , ∅ • fᶜ (inj₁ vsᶜ) , s₂'▸s = inj₁ (vsᶜ >≐> idemₛ (mapAll rᶜ→sr all₂ ) s₂'▸s >≐> sv)
...      | s₂' , ∅ • fᶜ (inj₂ ssᶜ) , s₂'▸s = inj₂ $ lemma2-2-f (s₀▸s₁ • f vv vs)            >≐>
                                                    idemₛ (mapAll w→sr all₁) s₁▸s₂          >≐>
                                                    ssᶜ >≐> idemₛ (mapAll rᶜ→sr all₂) s₂'▸s >≐> sv

module CrashDeterminacy
  (runSpec : (t : State) (ac : Action) → ∃[ t' ] (t ⟦ ac ⟧▸ t'))
  (RawStateᴾ : Set) (_⟦_⟧ᴿ▸_ : RawStateᴾ → Action → RawStateᴾ → Set)
  (RI CI : RawStateᴾ → Set)
  (AR CR : RawStateᴾ → State → Set)
  (RIRI : {s s' : RawStateᴾ} {ac : Action} → NormalSuccess ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → RI s')
  (ARAR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → NormalSuccess ac
        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → AR s' t')
  (RICI : {s s' : RawStateᴾ} {ac : Action} → NormalCrash ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → CI s')
  (ARCR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → NormalCrash ac
        → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → CR s' t')
  (CIRI : {s s' : RawStateᴾ} → s ⟦ r ⟧ᴿ▸ s' → CI s → RI s')
  (CRAR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ r ⟧ᴿ▸ s' → t ⟦ r ⟧▸ t' → CI s × CR s t → AR s' t')
  (CICI : {s s' : RawStateᴾ} → s ⟦ rᶜ ⟧ᴿ▸ s' → CI s → CI s')
  (CRCR : {s s' : RawStateᴾ} {t t' : State} → s ⟦ rᶜ ⟧ᴿ▸ s' → t ⟦ rᶜ ⟧▸ t' → CI s × CR s t → CR s' t')
  (read : RawStateᴾ → Addr → Data)
  (ObsEquiv : {s : RawStateᴾ} {t : State} → RI s × AR s t → read s ≐ State.volatile t)
  (Init : RawStateᴾ → Set)
  (init : (s : RawStateᴾ) → Init s → ∃[ t ] (RI s × AR s t))
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

  data Inv (rs : RawStateᴾ) : Set where
    normal : RI rs → Inv rs
    crash  : CI rs → Inv rs

  Stateᴾ : Set
  Stateᴾ = Σ[ rs ∈ RawStateᴾ ] Inv rs

  variable
    s    : Stateᴾ
    s'   : Stateᴾ
    s''  : Stateᴾ
    s''' : Stateᴾ
    s′   : Stateᴾ
    s″   : Stateᴾ
    s‴   : Stateᴾ

  data _⟦_⟧ᴾ▸_ : Stateᴾ → Action → Stateᴾ → Set where
    w  : rs ⟦ w[ addr ↦ dat ] ⟧ᴿ▸ rs' → (rs , normal rinv) ⟦ w[ addr ↦ dat ] ⟧ᴾ▸ (rs' , normal rinv')
    f  : rs ⟦ f  ⟧ᴿ▸ rs' → (rs , normal rinv) ⟦ f  ⟧ᴾ▸ (rs' , normal rinv')
    wᶜ : rs ⟦ wᶜ ⟧ᴿ▸ rs' → (rs , normal rinv) ⟦ wᶜ ⟧ᴾ▸ (rs' , crash  cinv')
    fᶜ : rs ⟦ fᶜ ⟧ᴿ▸ rs' → (rs , normal rinv) ⟦ fᶜ ⟧ᴾ▸ (rs' , crash  cinv')
    rᶜ : rs ⟦ rᶜ ⟧ᴿ▸ rs' → (rs , crash  cinv) ⟦ rᶜ ⟧ᴾ▸ (rs' , crash  cinv')
    r  : rs ⟦ r  ⟧ᴿ▸ rs' → (rs , crash  cinv) ⟦ r  ⟧ᴾ▸ (rs' , normal rinv')

  _⟦_⟧ᴾ*▸_ = RTC _⟦_⟧ᴾ▸_

  data SR : Stateᴾ → State → Set where
    ar : AR rs t → SR (rs , normal rinv) t
    cr : CR rs t → SR (rs , crash  cinv) t

  record SimSR (s : Stateᴾ) (t : State) : Set where
    coinductive
    field
      curr : SR s t
      next : ∀ {s'} → s ⟦ ac ⟧ᴾ▸ s' → ∃[ t' ] (t ⟦ ac ⟧▸ t' × SimSR s' t')

  simSR : (s : Stateᴾ) (t : State) → SR s t → SimSR s t
  SimSR.curr (simSR s t SR-s-t) = SR-s-t
  SimSR.next (simSR (rs , normal rinv) t (ar AR-rs-t)) (w {addr = addr} {dat = dat} rs▸rs') =
    let (t' , t▸t') = runSpec t w[ addr ↦ dat ]
    in   t' , t▸t' , simSR _ t' (ar (ARAR w rs▸rs' t▸t' (rinv , AR-rs-t)))
  SimSR.next (simSR (rs , normal rinv) t (ar AR-rs-t)) (f rs▸rs') =
    let (t' , t▸t') = runSpec t f
    in   t' , t▸t' , simSR _ t' (ar (ARAR f rs▸rs' t▸t' (rinv , AR-rs-t)))
  SimSR.next (simSR (rs , normal rinv) t (ar AR-rs-t)) (wᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t wᶜ
    in   t' , t▸t' , simSR _ t' (cr (ARCR wᶜ rs▸rs' t▸t' (rinv , AR-rs-t)))
  SimSR.next (simSR (rs , normal rinv) t (ar AR-rs-t)) (fᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t fᶜ
    in   t' , t▸t' , simSR _ t' (cr (ARCR fᶜ rs▸rs' t▸t' (rinv , AR-rs-t)))
  SimSR.next (simSR (rs , crash cinv) t (cr CR-rs-t)) (rᶜ rs▸rs') =
    let (t' , t▸t') = runSpec t rᶜ
    in   t' , t▸t' , simSR _ t' (cr (CRCR rs▸rs' t▸t' (cinv , CR-rs-t)))
  SimSR.next (simSR (rs , crash cinv) t (cr CR-rs-t)) (r rs▸rs') =
    let (t' , t▸t') = runSpec t r
    in   t' , t▸t' , simSR _ t' (ar (CRAR rs▸rs' t▸t' (cinv , CR-rs-t)))

  runSimSR : SimSR s t → s ⟦ ef ⟧ᴾ*▸ s' → ∃[ t' ] (t ⟦ ef ⟧*▸ t' × SimSR s' t')
  runSimSR sim-s-t ∅                 = _ , ∅ , sim-s-t
  runSimSR sim-s-t (s*▸s'' • s''▸s') =
    let (t'' , t*▸t'' , sim-s''-t'') = runSimSR sim-s-t s*▸s''
        (t'  , t''▸t' , sim-s'-t'  ) = SimSR.next sim-s''-t'' s''▸s'
    in  _ , (t*▸t'' • t''▸t') , sim-s'-t'

  lemma1-wᶜ : All NormalSuccess ef₁ → All Write ef₂ → All RecoveryCrash ef₃ →
                SimSR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s'' →
                read (proj₁ s') ≐ read (proj₁ s'')
  lemma1-wᶜ all₁ all₂ all₃ sim-s-t (s*▸ • f {rinv' = rinv'} ▸rs') (s'*▸ • r {rinv' = rinv''} ▸rs'')
    with runSimSR sim-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
  ...  | t'  , t*▸t'   , sim-s'-t'
    with runSimSR sim-s'-t' (s'*▸ • r {rinv' = rinv''} ▸rs'')
  ...  | t'' , t'*▸t'' , sim-s''-t''
    with SimSR.curr sim-s'-t' | SimSR.curr sim-s''-t''
  ...  | ar AR-rs'-t'         | ar AR-rs''-t'' =
                                  ObsEquiv (rinv' , AR-rs'-t')            >≐>
                                  lemma-2-wᶜ all₁ all₂ all₃ t*▸t' t'*▸t'' >≐>
                                  sym-≐ (ObsEquiv (rinv'' , AR-rs''-t''))

  lemma1-fᶜ : All NormalSuccess ef₁ → All Write ef₂ → All RecoveryCrash ef₃ →
                SimSR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ ⟧ᴾ*▸ s'' →  s'' ⟦ [] • fᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s''' →
                read (proj₁ s') ≐ read (proj₁ s''') ⊎ read (proj₁ s'') ≐ read (proj₁ s''')
  lemma1-fᶜ {ef₃ = ef₃} all₁ all₂ all₃ sim-s-t (s*▸ • f {rinv' = rinv'} ▸rs') rs'▸rs'' (rs''▸ • r {rinv' = rinv'''} ▸rs''')
    with splitRTC ([] • fᶜ) ef₃ rs''▸
  ...  | rs''₁ , ∅ • fᶜ {rinv = rinv''} rs''▸rs''₁ , rs''₁▸rs''₂
    with runSimSR sim-s-t (s*▸ • f {rinv' = rinv'} ▸rs')
  ...  | t'   , t*▸t'     , sim-s'-t'
    with runSimSR sim-s'-t' rs'▸rs''
  ...  | t''  , t'*▸t''   , sim-s''-t''
    with runSimSR sim-s''-t'' (rs''▸ • r {rinv' = rinv'''} ▸rs''')
  ...  | t''' , t''*▸t''' , sim-s'''-t'''
    with SimSR.curr sim-s'-t' | SimSR.curr sim-s''-t'' | SimSR.curr sim-s'''-t'''
  ...  | ar AR-rs'-t'         | ar AR-rs''-t''         | ar AR-rs'''-t'''
    with lemma-2-fᶜ all₁ all₂ all₃ t*▸t' t'*▸t'' t''*▸t'''
  ...  | inj₁ succ = inj₂ $ ObsEquiv (rinv'' , AR-rs''-t'') >≐>
                            succ >≐> sym-≐ (ObsEquiv (rinv''' , AR-rs'''-t'''))
  ...  | inj₂ fail = inj₁ $ ObsEquiv (rinv' , AR-rs'-t') >≐>
                            fail >≐> sym-≐ (ObsEquiv (rinv''' , AR-rs'''-t'''))

  initialisation : Init rs → ∃[ rinv ] ∃[ t ] SimSR (rs , normal rinv) t
  initialisation init-rs = let (t , RI-rs , AR-rs-t) = init _ init-rs
                           in  RI-rs , t , simSR _ t (ar AR-rs-t)

  lift-wf : All NormalSuccess ef → rs ⟦ ef ⟧ᴿ*▸ rs' →
            ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
  lift-wf all ∅ = _ , ∅
  lift-wf (all ∷ w) (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-wf all rs*▸rs''
    in  RIRI w rs''▸rs' rinv'' , s*▸s'' • w rs''▸rs'
  lift-wf (all ∷ f) (rs*▸rs'' • rs''▸rs') =
    let (rinv'' , s*▸s'') = lift-wf all rs*▸rs''
    in  RIRI f rs''▸rs' rinv'' , s*▸s'' • f rs''▸rs'

  lift-w : All Write ef → rs ⟦ ef ⟧ᴿ*▸ rs' →
           ∃[ rinv' ] ((rs , normal rinv) ⟦ ef ⟧ᴾ*▸ (rs' , normal rinv'))
  lift-w all rs*▸rs' = lift-wf (mapAll (λ{w → w}) all) rs*▸rs'

  lift-rᶜ : All RecoveryCrash ef → rs ⟦ ef ⟧ᴿ*▸ rs' →
            ∃[ cinv' ] ((rs , crash cinv) ⟦ ef ⟧ᴾ*▸ (rs' , crash cinv'))
  lift-rᶜ all ∅ = _ , ∅
  lift-rᶜ (all ∷ rᶜ) (rs*▸rs'' • rs''▸rs') =
    let (cinv'' , s*▸s'') = lift-rᶜ all rs*▸rs''
    in  CICI rs''▸rs' cinv'' , s*▸s'' • rᶜ rs''▸rs'

--   ef₁   f   ef₂    wᶜ    ef₃    r
-- rs   rs₁ rs'   rs'₁  rs'₂   rs'₃ rs''
  theorem-wᶜ : All NormalSuccess ef₁ → All Write ef₂ → All RecoveryCrash ef₃ →
             Init rs → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴿ*▸ rs'' →
             read rs' ≐ read rs''
  theorem-wᶜ {ef₁} {ef₂} {ef₃} all₁ all₂ all₃ i rs*▸rs' (rs'▸rs'₃ • r▸rs'')
      with splitRTC (ef₂ • wᶜ) ef₃ rs'▸rs'₃
  ...    | rs'₁ , rs'▸rs'₁ • wᶜ▸rs'₂ , rs'₁▸rs'₃ =
             let init-ri , init-t , init-ef = initialisation i
                 wf-ri   , wf-ef            = lift-wf (all₁ ∷ f) rs*▸rs'
                 w-ri    , w-ef             = lift-w  all₂ rs'▸rs'₁
                 rᶜ-ci   , rᶜ-ef            = lift-rᶜ all₃ rs'₁▸rs'₃
             in  lemma1-wᶜ all₁ all₂ all₃ init-ef wf-ef
                           (w-ef  • wᶜ {cinv' = RICI wᶜ wᶜ▸rs'₂ w-ri}  wᶜ▸rs'₂ ++RTC
                            rᶜ-ef • r  {rinv' = CIRI    r▸rs''  rᶜ-ci} r▸rs'')

--   ef₁   f   ef₂    fᶜ     ef₃     r
-- rs   rs₁ rs'   rs''  rs''₁   rs''₂ rs'''
  theorem-fᶜ : All NormalSuccess ef₁ → All Write ef₂ → All RecoveryCrash ef₃ →
             Init rs → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ ⟧ᴿ*▸ rs'' → rs'' ⟦ ([] • fᶜ) ⊙ ef₃ • r ⟧ᴿ*▸ rs''' →
             read rs' ≐ read rs''' ⊎ read rs'' ≐ read rs'''
  theorem-fᶜ {ef₁} {ef₂} {ef₃} all₁ all₂ all₃ i rs*▸rs' rs'▸rs'' (rs''▸rs''₂ • r▸rs''')
      with splitRTC ([] • fᶜ) ef₃ rs''▸rs''₂
  ...    | rs''₁ , ∅ • fᶜ▸rs''₁ , rs''₁▸rs''₂
      with let init-ri , init-t , init-ef = initialisation i
               wf-ri   , wf-ef            = lift-wf (all₁ ∷ f) rs*▸rs'
               w-ri    , w-ef             = lift-w  all₂ rs'▸rs''
               rᶜ-ci   , rᶜ-ef            = lift-rᶜ all₃ rs''₁▸rs''₂
           in  lemma1-fᶜ all₁ all₂ all₃ init-ef wf-ef w-ef
                         (∅     • fᶜ {cinv' = RICI fᶜ fᶜ▸rs''₁ w-ri} fᶜ▸rs''₁ ++RTC
                          rᶜ-ef • r  {rinv' = CIRI r▸rs''' rᶜ-ci}    r▸rs''')
  ...    | inj₁ succ = inj₁ succ
  ...    | inj₂ fail = inj₂ fail
