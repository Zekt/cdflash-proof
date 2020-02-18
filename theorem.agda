open import Data.Bool

module theorem (Addr : Set) (_=?_ : Addr -> Addr -> Bool) (Data : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; uncurry) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec
open import Function using (_$_)

infixl 20 _∙_
infixl 20 _⊙_
infixr 100 _[_↦_]
--infixr 20 _✗←✗_
--infixr 20 _✓←✗_
--infixr 20 _✗←✓_
--infixr 20 _✓←✓_


data Action : Set where
  w[_↦_] : Addr → Data → Action
  f      :               Action
  r      :               Action
  w✗     :               Action
  f✗     :               Action
  r✗     :               Action

data isSR : Action → Set where -- disjoint union of stable reserving actions
  cw  : {ac : Action} {addr : Addr} {dat : Data} → ac ≡ w[ addr ↦ dat ] → isSR w[ addr ↦ dat ]
  cr  : {ac : Action} → ac ≡ r  → isSR r
  cw✗ : {ac : Action} → ac ≡ w✗ → isSR w✗
  cf✗ : {ac : Action} → ac ≡ f✗ → isSR f✗
  cr✗ : {ac : Action} → ac ≡ r✗ → isSR r✗

data Success : Action → Set where -- disjoint union of success functions
  cw : {ac : Action} {addr : Addr} {dat : Data} → ac ≡ w[ addr ↦ dat ] → Success w[ addr ↦ dat ]
  cf : {ac : Action} → ac ≡ f → Success f
  cr : {ac : Action} → ac ≡ r → Success r

data Crash : Action → Set where -- disjoint union of crash functions
  cw✗ : {ac : Action} → ac ≡ w✗ → Crash w✗
  cf✗ : {ac : Action} → ac ≡ f✗ → Crash f✗
  cr✗ : {ac : Action} → ac ≡ r✗ → Crash r✗

data Crash* : Action → Set where -- disjoint union of crash functions we care
  cw✗ : {ac : Action} → ac ≡ w✗ → Crash* w✗
  cf✗ : {ac : Action} → ac ≡ f✗ → Crash* f✗

--data Fragment (t : Ft) : Set where
--  §_   : Action                    → Fragment t
--  _∙_  : Fragment t → Action       → Fragment t
--  _⊙_  : Fragment t → Fragment t   → Fragment t
--  _^_  : Action     → ℕ            → Fragment t
--  ⟦_⟧v : {n : ℕ}    → Vec Action n → Fragment t

--red : {s t : Ft} → Fragment s → Fragment t
--red (§ ac)     = § ac
--red (ff ∙ x)   = red ff ∙ x
--red (ff ⊙ ff₁) = red ff ⊙ red ff₁
--red (x ^ n)    = x ^ n
--red ⟦ xs ⟧v    = ⟦ xs ⟧v

--data _<=>_ (a : Fragment prog) (b : Fragment spec) : Set where
--  redeq : red a ≡ b → a <=> b

record State : Set where
  constructor ⟨_,_⟩
  field
    volatile : Addr -> Data
    stable   : Addr -> Data
 
_[_↦_] : (Addr -> Data) -> Addr -> Data -> (Addr -> Data)
(s [ addr ↦ dat ]) i with addr =? i
...                  | true  = dat
...                  | false = s i

_==_ : (Addr -> Data) -> (Addr -> Data) -> Set
s == t = ∀ (addr : Addr) -> s addr ≡ t addr

sym-== : ∀ {s t : Addr → Data} → s == t → t == s
sym-== eq = λ{x → sym (eq x)}

tran-== : ∀ {s t u : Addr → Data} → s == t → t == u → s == u
tran-== e q = λ{x → begin s x ≡⟨ e x ⟩ t x ≡⟨ q x ⟩ u x ∎}

--data _==_ : (Addr -> Data) -> (Addr -> Data) -> Set where
--  eq : {s t : Addr -> Data} -> (∀ addr -> s addr ≡ t addr) -> s == t

--data State : Set where
--  vlt₀     :                 State
--  stb₀     :                 State
--  mod      : State →         State -- TODO maybe not accurate
--  _[_↦_]   : State → ℕ → ℕ → State -- XXX not really useful

-- TODO Is relation better?
data _⟦_⟧▸_ : State → Action → State → Set where
  _w[_↦_]▸_ : (s s' : State) (addr : Addr) (dat : Data) → State.volatile s [ addr ↦ dat ] == State.volatile s'
                                                        → State.stable s == State.stable s'
                                                        → s ⟦ w[ addr ↦ dat ] ⟧▸ s'
  _f▸_ : (s s' : State) → State.volatile s == State.volatile s'
                        → State.volatile s == State.stable s'
                        → s ⟦ f ⟧▸ s'
  _r▸_ : (s s' : State) → State.stable s == State.volatile s'
                        → State.stable s == State.stable s'
                        → s ⟦ r ⟧▸ s'
  _w✗▸_ : (s s' : State) → State.stable s == State.stable s'
                         → s ⟦ w✗ ⟧▸ s'
  _f✗▸_ : (s s' : State) → State.volatile s == State.stable s' ⊎ State.stable s == State.stable s'
                         → s ⟦ f✗ ⟧▸ s'
  _r✗▸_ : (s s' : State) → State.stable s == State.stable s'
                         → s ⟦ r✗ ⟧▸ s'

--data SnocList (A : Set) : Set where
--  []  : SnocList A
--  _∙_ : SnocList A → A → SnocList A

data Ft : Set where
  prog : Ft
  spec : Ft

data Fragment (t : Ft) : Set where
  []  : Fragment t
  _∙_ : Fragment t → Action → Fragment t

data All (P : Action → Set) : {t : Ft} → Fragment t → Set where
  []  : All P []
  _∷_ : ∀ {x : Action} {t : Ft} {xs : Fragment t} → All P xs → P x → All P (xs ∙ x)
--_⊙_ : {A : Set} → SnocList A -> SnocList A -> SnocList A
--xs ⊙ []       = xs
--xs ⊙ (ys ∙ y) = (xs ⊙ ys) ∙ y
_⊙_ : {t : Ft} → Fragment t → Fragment t → Fragment t
xs ⊙ []       = xs
xs ⊙ (ys ∙ y) = (xs ⊙ ys) ∙ y

data _⟦_⟧*▸_ : State → {t : Ft} → Fragment t → State → Set where
  ∅   : ∀ {s s' : State} → s ⟦ [] ⟧*▸ s'
  _∙_ : ∀ {s t u : State} {ft : Ft} {acts : Fragment ft} {act : Action}
      → s ⟦ acts ⟧*▸ t → t ⟦ act ⟧▸ u → s ⟦ acts ∙ act ⟧*▸ u


--⟦_⟧p : Action → State × State → State × State
--⟦ w   ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
--⟦ f   ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
--⟦ r   ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
--⟦ w✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
--⟦ f✗₁ ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
--⟦ f✗₂ ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , vlt ⟩
--⟦ r✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
--
--runFragment : State × State → Fragment spec → State × State
--runFragment s (§ ac)       = ⟦ ac ⟧p ⟨ vlt₀ , stb₀ ⟩
--runFragment s (ef ∙ ac)    = ⟦ ac ⟧p (runFragment s ef)
--runFragment s (ef₁ ⊙ ef₂)  = runFragment (runFragment s ef₁) ef₂
--runFragment s (ac ^ zero)  = s
--runFragment s (ac ^ suc n) = ⟦ ac ⟧p (runFragment s (ac ^ n))
--runFragment s ⟦ [] ⟧v      = s
--runFragment s ⟦ x ∷ xs ⟧v  = runFragment (⟦ x ⟧p s) ⟦ xs ⟧v
--
--data SR : Fragment spec → Fragment spec → Set where -- Stable Reservation
--  sr : {frag₁ frag₂ : Fragment spec}
--     → (∀ {s s₁ s₂ : State} → s ⟦ frag₁ ⟧*▸ s₁ -> s ⟦ frag₂ ⟧*▸ s₂ → State.stable s₁ == State.stable s₂)
--     → SR frag₁ frag₂
--sr : {ef₁ ef₂ : Fragment spec}
--   → proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₁) ≡ proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₂)
--   → SR ef₁ ef₂
--
--data VR : Fragment spec → Fragment spec → Set where -- Volatile Reservation
--  vr : {frag₁ frag₂ : Fragment spec}
--     → (∀ {s s₁ s₂ : State} → s ⟦ frag₁ ⟧*▸ s₁ → s ⟦ frag₂ ⟧*▸ s₂ → State.volatile s₁ == State.volatile s₂)
--     → VR frag₁ frag₂

v=s : ∀ (ac : Action) → (ac ≡ f ⊎ ac ≡ r)
    → ∀ {s s' : State} → s ⟦ ac ⟧▸ s'
    → State.volatile s' == State.stable s'
v=s .f (inj₁ refl) ((s f▸ s') x x₁) = λ{x → {! !}}
v=s .r (inj₂ refl) abc = {!   !}
--v=s .f (inj₁ refl) ef = refl
--v=s .r (inj₂ refl) ef = refl


--lem-⊙ : ∀ (ef₁ ef₂ : Fragment spec)
--      → ( ∀ (s : State × State) → proj₂ (runFragment s ef₂) ≡ proj₂ s )
--      → ∀ (t : State × State) → proj₂ (runFragment t (ef₁ ⊙ ef₂)) ≡ proj₂ (runFragment t ef₁)
--lem-⊙ ef₁ ef₂ lem t = begin
--                        proj₂ (runFragment t (ef₁ ⊙ ef₂))
--                      ≡⟨ lem (runFragment t ef₁) ⟩
--                        proj₂ (runFragment t ef₁)
--                      ∎
--
s^n=s : ∀ {ac : Action} → isSR ac
      → ∀ {frag : Fragment spec} → All (λ{x → x ≡ ac}) frag
      → ∀ (s s' : State) → s ⟦ frag ⟧*▸ s'
      → State.stable s == State.stable s'
--s^n=s _        zero    s = refl
--s^n=s (cw x)   (suc n) s = s^n=s (cw x)   n s
--s^n=s (cr x)   (suc n) s = s^n=s (cr x)   n s
--s^n=s (cw✗ x)  (suc n) s = s^n=s (cw✗ x)  n s
--s^n=s (cf✗₁ x) (suc n) s = s^n=s (cf✗₁ x) n s
--s^n=s (cr✗ x)  (suc n) s = s^n=s (cr✗ x)  n s
--
--lem-sr : ∀ {ac : Action} → isSR ac → ∀ (ef : Fragment spec) → ∀ (n : ℕ)
--        → ∀ (s : State × State) → proj₂ ( runFragment s (ef ⊙ (ac ^ n)) ) ≡ proj₂ ( runFragment s ef )
--lem-sr {ac} du ef n s = begin
--                    proj₂ ( runFragment s (ef ⊙ (ac ^ n)) )
--                  ≡⟨ lem-⊙ ef (ac ^ n) (s^n=s du n) s ⟩
--                    proj₂ ( runFragment s ef )
--                  ∎
--
lemma2-1 : ∀ {ac : Action} → isSR ac
         → ∀ (frag-w frag-r✗ : Fragment spec)
         → ∀ {addr : Addr} {dat : Data} → All (λ{x → x ≡ w[ addr ↦ dat ]}) frag-w → All (λ{x → x ≡ r✗}) frag-r✗
         → ∀ (s s' : State) → s ⟦ frag-w ∙ ac ⊙ frag-r✗ ⟧*▸ s'
         → State.stable s == State.stable s'
--lemma2-1 {ac} du ef₁ ef₂ m n refl = sr ( sym
--       let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
--       begin
--         proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n)) )
--       ≡⟨ lem-sr (cr✗ refl)  (ef₁ ⊙ (w ^ m) ∙ ac) n s₀ ⟩
--         proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ ac) )
--       ≡⟨ lem-sr du (ef₁ ⊙ (w ^ m)) 1 s₀ ⟩
--         proj₂ (runFragment s₀ (ef₁ ⊙ (w ^ m)))
--       ≡⟨ lem-sr (cw refl) ef₁ m s₀ ⟩
--         proj₂ (runFragment s₀ ef₁)
--       ∎
--       )
--
--lemma2-1-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec)
--             → ∀ (m n : ℕ) → ef₁ ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n) ≡ ef₂
--             ∀ (ads : SnocList (Addr × Data)) -> ef₁ ⊙ map (uncurry w) ads
--             → SR (ef₁ ⊙ (w ^ m) ∙ f✗₂) ef₂
--lemma2-1-f✗₂ ef₁ ef₂ m n refl = sr ( sym
--        let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
--        begin
--          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n)) )
--        ≡⟨ lem-sr (cr✗ refl) (ef₁ ⊙ (w ^ m) ∙ f✗₂) n s₀ ⟩
--          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂) )
--        ∎
--        )
lemma-2-2 : ∀ (s t t' : State) → State.stable s == State.stable t → t ⟦ r ⟧▸ t'
          → State.volatile s == State.volatile t'
--lemma2-2 : ∀ (ef₁ ef₂ : Fragment spec) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
--lemma2-2 ef₁ ef₂ (sr x) = vr (
--                         let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
--                         begin
--                           proj₁ (runFragment s₀ (ef₁ ∙ f))
--                         ≡⟨ v=s f (inj₁ refl) ef₁ ⟩
--                           proj₂ (runFragment s₀ (ef₁ ∙ f))
--                         ≡⟨ x ⟩
--                           proj₁ (runFragment s₀ (ef₂ ∙ r))
--                         ∎
--                         )
--
--lemma2-2-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec) → SR (ef₁ ∙ f✗₂) ef₂ → VR ef₁ (ef₂ ∙ r)
--lemma2-2-f✗₂ ef₁ ef₂ (sr x) = vr (
--                            let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
--                            begin
--                              proj₁ (runFragment s₀ ef₁)
--                            ≡⟨ x ⟩
--                              proj₁ (runFragment s₀ (ef₂ ∙ r))
--                            ∎
--                            )
lemma-2 : ∀ (ac : Action) → Crash* ac
        → ∀ (s s' : State) → ∀ (frag-w frag-r✗)
        → ∀ {addr : Addr} {dat : Data} → All (λ{x → x ≡ w[ addr ↦ dat ]}) frag-w → All (λ{x → x ≡ r✗}) frag-r✗
        → s ⟦ [] ∙ f ⊙ frag-w ∙ ac ⊙ frag-r✗ ∙ r ⟧*▸ s'
        → State.volatile s == State.volatile s'
--lemma2-w✗ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
--          → ef₁ ∙ f ⊙ (w ^ m) ∙ w✗ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
--          → VR (ef₁ ∙ f) ef₂
--lemma2-w✗ ef₁ ef₂ m n refl = let ef₂-r = (ef₁ ∙ f ⊙ (w ^ m) ∙ w✗ ⊙ (r✗ ^ n))
--                             in  lemma2-2 ef₁ ef₂-r (lemma2-1 (cw✗ refl) (ef₁ ∙ f) ef₂-r m n refl)
--
--lemma2-f✗₁ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
--           → ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₁ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
--           → VR (ef₁ ∙ f) ef₂
--lemma2-f✗₁ ef₁ ef₂ m n refl = let ef₂-r = (ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₁ ⊙ (r✗ ^ n))
--                              in  lemma2-2 ef₁ ef₂-r (lemma2-1 (cf✗₁ refl) (ef₁ ∙ f) ef₂-r m n refl)
--
--lemma2-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
--           → ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
--           → VR (ef₁ ∙ f ⊙ (w ^ m)) ef₂
--lemma2-f✗₂ ef₁ ef₂ m n refl = let ef₁-new = ef₁ ∙ f ⊙ (w ^ m)
--                                  ef₂-r   = ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n)
--                              in  lemma2-2-f✗₂ ef₁-new ef₂-r (lemma2-1-f✗₂ (ef₁ ∙ f) ef₂-r m n refl)
--
---- lemma2 : ∀ (ef₁ ef₂ : Fragment spec) → ∀ {ac : Action} → Crash₂ ac → ∀ (m n : ℕ)
----        → ef₁ ∙ f ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n) ∙ r ≡ ef₂
----        → VR (ef₁ ∙ f) ef₂
---- lemma2 ef₁ ef₂ (cw✗ x) m n refl = lemma2-w✗ ef₁ ef₂ m n refl
---- lemma2 ef₁ ef₂ (cf✗₁ x) m n refl = lemma2-f✗₁ ef₁ ef₂ m n refl
---- lemma2 ef₁ ef₂ (cf✗₂ x) m n refl = lemma2-f✗₂ ef₁ ef₂ m n refl
--
--------
--
--data RI : Fragment prog → Set
--data CI : Fragment prog → Set
--data AR : Fragment prog → Fragment spec → Set
--data CR : Fragment prog → Fragment spec → Set
--
--data RI where -- Relation Invariance
--  ri✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → RI ef → RI (ef ∙ ac)
--  ci✓ : {ef : Fragment prog} → CI ef → RI (ef ∙ r)
--  id✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → (n : ℕ) → RI ef → RI (ef ⊙ (ac ^ n))
--  v✓  : {n : ℕ} → (v : Vec Action n) → All (λ{x → (x ≡ w ⊎ x ≡ f)}) v → RI ⟦ v ⟧v
--
--data CI where -- Crash Invariance
--  ri✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → RI ef → CI (ef ∙ ac)
--  ci✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → CI ef → CI (ef ∙ ac)
--  id✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → (n : ℕ) → CI ef → CI (ef ⊙ (ac ^ n))
--
---- Abstract Relation of efp(Fragmant of Prog) and efs(Fragment of Spec)
--data AR where
--  ar✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f)
--      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → AR (efp ∙ ac) (efs ∙ ac)
--  cr✓ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → AR (efp ∙ r) (efs ∙ r)
--  id✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {efp : Fragment prog} → {efs : Fragment spec}
--      → (n : ℕ) → RI efp → AR efp efs → AR (efp ⊙ (ac ^ n)) (efs ⊙ (ac ^ n))
--  v✓  : {n : ℕ} → (v : Vec Action n) → All (λ{x → (x ≡ w ⊎ x ≡ f)}) v → AR ⟦ v ⟧v ⟦ v ⟧v
--
---- Crash Relation
--data CR where
--  ar✗  : ∀ {ac : Action} → Crash ac
--      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → CR (efp ∙ ac) (efs ∙ ac)
--  cr✗ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → CR (efp ∙ r✗) (efs ∙ r✗)
--  id✗ : ∀ {ac : Action} → Crash ac → {efp : Fragment prog} → {efs : Fragment spec}
--      → (n : ℕ) → CI efp → CR efp efs → CR (efp ⊙ (ac ^ n)) (efs ⊙ (ac ^ n))
--
---- Observational Equivalence -- TODO Is this ok?
--data OE : Fragment prog → Fragment spec → Set where
--  oe : {efp : Fragment prog} → {efs : Fragment spec} → RI efp × AR efp efs → OE efp efs
----tran : {efp : Fragment prog} → {efs₁ efs₂ : Fragment spec} → VR efs₁ efs₂ → OE efp efs₂ → OE efp efs₁
--
---- FIXME maybe problematic
--data CD : Fragment prog → Fragment prog → Set where
--  cd : {efp₁ efp₂ : Fragment prog} → {efs₁ efs₂ : Fragment spec}
--     → VR efs₁ efs₂ → OE efp₁ efs₁ → OE efp₂ efs₂ → CD efp₁ efp₂
--
--
--_✓←✗_ : {a b : Fragment prog} {a' b' : Fragment spec}
--      → (CI a → RI b) × (CI a → CR a a' → AR b b') → (CI a × CR a a') → RI b × AR b b'
--⟨ g , h ⟩ ✓←✗ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩
--
--_✗←✗_ : {a b : Fragment prog} {a' b' : Fragment spec}
--      → (CI a → CI b) × (CI a → CR a a' → CR b b') → (CI a × CR a a') → CI b × CR b b'
--⟨ g , h ⟩ ✗←✗ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩
--
--_✗←✓_ : {a b : Fragment prog} {a' b' : Fragment spec}
--      → (RI a → CI b) × (RI a → AR a a' → CR b b') → (RI a × AR a a') → CI b × CR b b'
--⟨ g , h ⟩ ✗←✓ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩
--
--_✓←✓_ : {a b : Fragment prog} {a' b' : Fragment spec}
--      → (RI a → RI b) × (RI a → AR a a' → AR b b') → (RI a × AR a a') → RI b × AR b b'
--⟨ g , h ⟩ ✓←✓ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩
--
--lemma1 : ∀ (efp : Fragment prog) → ∀ {ac : Action} → Crash ac → ∀ (i j k : ℕ)
--       → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
--       → efp ≡ (⟦ v ⟧v) ∙ f ⊙ (w ^ j) ∙ ac ⊙ (r✗ ^ k) ∙ r
--       → ∃[ efs ] ( efp <=> efs × (RI efp × AR efp efs) ) -- efs : Fragment spec
--lemma1 efp du i j k v all refl = ⟨ red efp , ⟨ redeq refl
--                                             , ⟨ ci✓               , cr✓               ⟩
--                                           ✓←✗ ⟨ id✗ (cr✗ refl) k  , id✗ (cr✗ refl) k  ⟩
--                                           ✗←✗ ⟨ ri✗ du            , ar✗ du            ⟩
--                                           ✗←✓ ⟨ id✓ (inj₁ refl) j , id✓ (inj₁ refl) j ⟩
--                                           ✓←✓ ⟨ ri✓ (inj₂ refl)   , ar✓ (inj₂ refl)   ⟩
--                                           ✓←✓ ⟨ v✓ v all          , v✓ v all          ⟩
--                                             ⟩ ⟩
--
---- theorem : ∀ (efp : Fragment prog)
----         → ∀ {ac : Action} → Crash₂ ac → ∀ (i j k : ℕ)
----         → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
----         → efp ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ ac ⊙ (r✗ ^ k) ∙ r
----         → ∃[ efs ] (OE efp efs)
---- theorem efp (cw✗ x)  i j k v all refl = ⟨ ⟦ v ⟧v ∙ f
----                                         , tran (lemma2-w✗ (⟦ v ⟧v) (red efp) j k refl)
----                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cw✗ x) i j k v all refl)
----                                         ⟩
---- theorem efp (cf✗₁ x) i j k v all refl = ⟨ ⟦ v ⟧v ∙ f
----                                         , tran (lemma2-f✗₁ (⟦ v ⟧v) (red efp) j k refl)
----                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cf✗₁ x) i j k v all refl)
----                                         ⟩
---- theorem efp (cf✗₂ x) i j k v all refl = ⟨ ⟦ v ⟧v ∙ f ⊙ (w ^ j)
----                                         , tran (lemma2-f✗₂ (⟦ v ⟧v) (red efp) j k refl)
----                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cf✗₂ x) i j k v all refl)
----                                         ⟩
--
--theorem-w✗ : ∀ (efp₁ efp₂ : Fragment prog)
--           → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
--           → efp₁ ≡ ⟦ v ⟧v ∙ f
--           → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ w✗ ⊙ (r✗ ^ k) ∙ r
--           → CD efp₁ efp₂
--theorem-w✗ efp₁ efp₂ i j k v all refl refl = cd (lemma2-w✗ (⟦ v ⟧v) (red efp₂) j k refl)
--                                                (oe (    ⟨ ri✓ (inj₂ refl) , ar✓ (inj₂ refl) ⟩
--                                                     ✓←✓ ⟨ v✓ v all        , v✓ v all        ⟩))
--                                                (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cw✗ refl) i j k v all refl)
--
--theorem-f✗₁ : ∀ (efp₁ efp₂ : Fragment prog)
--            → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
--            → efp₁ ≡ ⟦ v ⟧v ∙ f
--            → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ f✗₁ ⊙ (r✗ ^ k) ∙ r
--            → CD efp₁ efp₂
--theorem-f✗₁ efp efp₂ i j k v all refl refl = cd (lemma2-f✗₁ (⟦ v ⟧v) (red efp₂) j k refl)
--                                                (oe (    ⟨ ri✓ (inj₂ refl) , ar✓ (inj₂ refl) ⟩
--                                                     ✓←✓ ⟨ v✓ v all        , v✓ v all        ⟩))
--                                                (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cf✗₁ refl) i j k v all refl)
--
--theorem-f✗₂ : ∀ (efp₁ efp₂ : Fragment prog)
--            → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
--            → efp₁ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j)
--            → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ f✗₂ ⊙ (r✗ ^ k) ∙ r
--            → CD efp₁ efp₂
--theorem-f✗₂ efp₁ efp₂ i j k v all refl refl = cd (lemma2-f✗₂ (⟦ v ⟧v) (red efp₂) j k refl)
--                                                 (oe (    ⟨ id✓ (inj₁ refl) j , id✓ (inj₁ refl) j ⟩
--                                                      ✓←✓ ⟨ ri✓ (inj₂ refl)   , ar✓ (inj₂ refl)   ⟩
--                                                      ✓←✓ ⟨ v✓ v all          , v✓ v all          ⟩))
--                                                 (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cf✗₂ refl) i j k v all refl)
