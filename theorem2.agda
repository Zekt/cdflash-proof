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
open import Function using (_$_)

infixl 20 _•_
infixl 20 _⊙_
infixl 20 _++RTC_
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

data Write : Action → Set where
  w : Write w[ addr ↦ dat ]

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

tran-≐ : ∀ {s t u : Addr → Data} → s ≐ t → t ≐ u → s ≐ u
tran-≐ {s} {t} {u} e q = λ{x → begin s x ≡⟨ e x ⟩ t x ≡⟨ q x ⟩ u x ∎}

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

module CrashDeterminacy
  (runSpec : (t : State) (ac : Action) → ∃[ t' ] (t ⟦ ac ⟧▸ t'))
  (RawStateᴾ : Set) (_⟦_⟧ᴿ▸_ : RawStateᴾ → Action → RawStateᴾ → Set)
  (RI CI : RawStateᴾ → Set)
  (AR CR : RawStateᴾ → State → Set)
  (RIRI : {s s' : RawStateᴾ} {ac : Action} → NormalSuccess ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → RI s')
  (ARAR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → NormalSuccess ac → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → AR s' t')
  (RICI : {s s' : RawStateᴾ} {ac : Action} → NormalCrash ac → s ⟦ ac ⟧ᴿ▸ s' → RI s → CI s')
  (ARCR : {s s' : RawStateᴾ} {t t' : State} {ac : Action} → NormalCrash ac → s ⟦ ac ⟧ᴿ▸ s' → t ⟦ ac ⟧▸ t' → RI s × AR s t → CR s' t')
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
    rinv' : RI rs'
    cinv' : CI rs'

  _⟦_⟧ᴿ*▸_ = RTC _⟦_⟧ᴿ▸_

  data Inv (rs : RawStateᴾ) : Set where
    normal : RI rs → Inv rs
    crash  : CI rs → Inv rs

  Stateᴾ : Set
  Stateᴾ = Σ[ rs ∈ RawStateᴾ ] Inv rs

  variable
    s   : Stateᴾ
    s'  : Stateᴾ
    s'' : Stateᴾ

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
  
  main-lemma1 : All NormalSuccess ef₁ → All Write ef₂ → All (λ ac → ac ≡ rᶜ) ef₃ →
                SimSR s t → s ⟦ ef₁ • f ⟧ᴾ*▸ s' → s' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴾ*▸ s'' →
                read (proj₁ s') ≐ read (proj₁ s'')
  main-lemma1 _ all₂ all₃ sim-s-t (s*▸ • f ▸rs') (s'*▸ • r {rinv' = rinv''} ▸rs'')
    with runSimSR sim-s-t (s*▸ • f ▸rs')
  ...  | t'  , t*▸t'   , sim-s'-t'
    with runSimSR sim-s'-t' (s'*▸ • r {rinv' = rinv''} ▸rs'')
  ...  | t'' , t'*▸t'' , sim-s''-t''
    with SimSR.curr sim-s'-t' | SimSR.curr sim-s''-t''
  ...  | ar AR-rs'-t' | ar AR-rs''-t'' = {!!}
  
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

  theorem1 : All NormalSuccess ef₁ → All Write ef₂ → All (λ ac → ac ≡ rᶜ) ef₃ →
             Init rs → rs ⟦ ef₁ • f ⟧ᴿ*▸ rs' → rs' ⟦ ef₂ • wᶜ ⊙ ef₃ • r ⟧ᴿ*▸ rs'' →
             read rs' ≐ read rs''
  theorem1 = {!!}
