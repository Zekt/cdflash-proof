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
infixr 20 _✗←✗_
infixr 20 _✓←✗_
infixr 20 _✗←✓_
infixr 20 _✓←✓_

data All {A : Set} (P : A → Set) : {n : ℕ} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {n : ℕ} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

data Action : Set where
  w   : Action
  f   : Action
  r   : Action
  w✗  : Action
  f✗₁ : Action
  f✗₂ : Action
  r✗  : Action

data isSR : Action → Set where -- disjoint union of stable reserving actions
  cw   : {ac : Action} → ac ≡ w   → isSR w
  cr   : {ac : Action} → ac ≡ r   → isSR r
  cw✗  : {ac : Action} → ac ≡ w✗  → isSR w✗
  cf✗₁ : {ac : Action} → ac ≡ f✗₁ → isSR f✗₁
  cr✗  : {ac : Action} → ac ≡ r✗  → isSR r✗

data Success : Action → Set where -- disjoint union of success functions
  cw : {ac : Action} → ac ≡ w → Success w
  cf : {ac : Action} → ac ≡ f → Success f
  cr : {ac : Action} → ac ≡ r → Success r

data Crash : Action → Set where -- disjoint union of crash functions
  cw✗  : {ac : Action} → ac ≡ w✗  → Crash w✗
  cf✗₁ : {ac : Action} → ac ≡ f✗₁ → Crash f✗₁
  cf✗₂ : {ac : Action} → ac ≡ f✗₂ → Crash f✗₂
  cr✗  : {ac : Action} → ac ≡ r✗  → Crash r✗

data Crash* : Action → Set where -- disjoint union of crash functions we care
  cw✗  : {ac : Action} → ac ≡ w✗  → Crash* w✗
  cf✗₁ : {ac : Action} → ac ≡ f✗₁ → Crash* f✗₁
  cf✗₂ : {ac : Action} → ac ≡ f✗₂ → Crash* f✗₂

data Ft : Set where
  prog : Ft
  spec : Ft

data Fragment (t : Ft) : Set where
  §_   : Action                    → Fragment t
  _∙_  : Fragment t → Action       → Fragment t
  _⊙_  : Fragment t → Fragment t   → Fragment t
  _^_  : Action     → ℕ            → Fragment t
  ⟦_⟧v : {n : ℕ}    → Vec Action n → Fragment t

red : {s t : Ft} → Fragment s → Fragment t
red (§ ac)     = § ac
red (ff ∙ x)   = red ff ∙ x
red (ff ⊙ ff₁) = red ff ⊙ red ff₁
red (x ^ n)    = x ^ n
red ⟦ xs ⟧v    = ⟦ xs ⟧v

data _<=>_ (a : Fragment prog) (b : Fragment spec) : Set where
  redeq : red a ≡ b → a <=> b

record State where
  constructor ⟨_,_⟩
  field
    volatile : Addr -> Data
    stable   : Addr -> Data
 
_[_↦_] : (Addr -> Data) -> Addr -> Data -> (Addr -> Data)
(s [ addr ↦ dat ]) i with addr =? i
...                  | true  = dat
...                  | false = s i

_==_ : (Addr -> Data) -> (Addr -> Data) -> Set
s == t = ∀ addr -> s addr ≡ t addr

data _==_ : (Addr -> Data) -> (Addr -> Data) -> Set where
  eq : {s t : Addr -> Data} -> (∀ addr -> s addr ≡ t addr) -> s == t

--data State : Set where
--  vlt₀     :                 State
--  stb₀     :                 State
--  mod      : State →         State -- TODO maybe not accurate
--  _[_↦_]   : State → ℕ → ℕ → State -- XXX not really useful

-- TODO Is relation better?
data _⟦_⟧▸_ : State → Action → State → Set where
   _w▸_ : (s s' : State) → State.volatile s [ addr ↦ dat ] == State.volatile s' -> State.stable s == State.stable s' → s ⟦ w ⟧▸ s'
   _f▸_ : (a b : State × State) → ⟨ proj₁ a ≡ proj₁ b , proj₁ a ≡ proj₂ b ⟩ → a ⟦ f ⟧▸ b

data SnocList ...

_⊙_ : SnocList A -> SnocList A -> SnocList A
xs ⊙ []       = xs
xs ⊙ (ys ∙ y) = (xs ⊙ ys) ∙ y

data _⟦_⟧*▸_: State -> SnocList Action -> State -> Set where
   ∅   : s ⟦ [] ⟧*▸ s'
   _∙_ : s ⟦ acts ⟧*▸ t -> t ⟦ act ⟧▸ u -> s ⟦ acts ∙ act ⟧*▸ u


⟦_⟧p : Action → State × State → State × State
⟦ w   ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
⟦ f   ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
⟦ r   ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
⟦ w✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
⟦ f✗₁ ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩
⟦ f✗₂ ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , vlt ⟩
⟦ r✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ mod vlt , stb ⟩

runFragment : State × State → Fragment spec → State × State
runFragment s (§ ac)       = ⟦ ac ⟧p ⟨ vlt₀ , stb₀ ⟩
runFragment s (ef ∙ ac)    = ⟦ ac ⟧p (runFragment s ef)
runFragment s (ef₁ ⊙ ef₂)  = runFragment (runFragment s ef₁) ef₂
runFragment s (ac ^ zero)  = s
runFragment s (ac ^ suc n) = ⟦ ac ⟧p (runFragment s (ac ^ n))
runFragment s ⟦ [] ⟧v      = s
runFragment s ⟦ x ∷ xs ⟧v  = runFragment (⟦ x ⟧p s) ⟦ xs ⟧v

data SR : Fragment spec → Fragment spec → Set where -- Stable Reservation
  sr : (∀ s s₁ s₂ -> s ⟦ frag₁ ⟧*▸ s₁ -> s ⟦ frag₂ ⟧*▸ s₂ -> State.stable s₁ == State.stable s₂) -> SR frag₁ frag₂
--  sr : {ef₁ ef₂ : Fragment spec}
--     → proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₁) ≡ proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₂)
--     → SR ef₁ ef₂

data VR : Fragment spec → Fragment spec → Set where -- Volatile Reservation
  vr : {ef₁ ef₂ : Fragment spec}
     → proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₁) ≡ proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₂)
     → VR ef₁ ef₂

v=s : ∀ (ac : Action) → (ac ≡ f ⊎ ac ≡ r)
    → ∀ (ef : Fragment spec)
    → proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ (ef ∙ ac)) ≡ proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ (ef ∙ ac))
v=s .f (inj₁ refl) ef = refl
v=s .r (inj₂ refl) ef = refl


lem-⊙ : ∀ (ef₁ ef₂ : Fragment spec)
       → ( ∀ (s : State × State) → proj₂ (runFragment s ef₂) ≡ proj₂ s )
       → ∀ (t : State × State) → proj₂ (runFragment t (ef₁ ⊙ ef₂)) ≡ proj₂ (runFragment t ef₁)
lem-⊙ ef₁ ef₂ lem t = begin
                        proj₂ (runFragment t (ef₁ ⊙ ef₂))
                      ≡⟨ lem (runFragment t ef₁) ⟩
                        proj₂ (runFragment t ef₁)
                      ∎

s^n=s : ∀ {ac : Action} → isSR ac
      → ∀ (n : ℕ) → ∀ (s : State × State) → proj₂ (runFragment s (ac ^ n)) ≡ proj₂ s
s^n=s _        zero    s = refl
s^n=s (cw x)   (suc n) s = s^n=s (cw x)   n s
s^n=s (cr x)   (suc n) s = s^n=s (cr x)   n s
s^n=s (cw✗ x)  (suc n) s = s^n=s (cw✗ x)  n s
s^n=s (cf✗₁ x) (suc n) s = s^n=s (cf✗₁ x) n s
s^n=s (cr✗ x)  (suc n) s = s^n=s (cr✗ x)  n s

lem-sr : ∀ {ac : Action} → isSR ac → ∀ (ef : Fragment spec) → ∀ (n : ℕ)
        → ∀ (s : State × State) → proj₂ ( runFragment s (ef ⊙ (ac ^ n)) ) ≡ proj₂ ( runFragment s ef )
lem-sr {ac} du ef n s = begin
                    proj₂ ( runFragment s (ef ⊙ (ac ^ n)) )
                  ≡⟨ lem-⊙ ef (ac ^ n) (s^n=s du n) s ⟩
                    proj₂ ( runFragment s ef )
                  ∎

lemma2-1 : ∀ {ac : Action} → isSR ac
         → ∀ (ef₁ ef₂ : Fragment spec)
         → ∀ (m n : ℕ) → ef₁ ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n) ≡ ef₂
         → SR ef₁ ef₂
lemma2-1 {ac} du ef₁ ef₂ m n refl = sr ( sym
       let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
       begin
         proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n)) )
       ≡⟨ lem-sr (cr✗ refl)  (ef₁ ⊙ (w ^ m) ∙ ac) n s₀ ⟩
         proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ ac) )
       ≡⟨ lem-sr du (ef₁ ⊙ (w ^ m)) 1 s₀ ⟩
         proj₂ (runFragment s₀ (ef₁ ⊙ (w ^ m)))
       ≡⟨ lem-sr (cw refl) ef₁ m s₀ ⟩
         proj₂ (runFragment s₀ ef₁)
       ∎
       )

lemma2-1-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec)
             → ∀ (m n : ℕ) → ef₁ ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n) ≡ ef₂
             ∀ (ads : SnocList (Addr × Data)) -> ef₁ ⊙ map (uncurry w) ads
             → SR (ef₁ ⊙ (w ^ m) ∙ f✗₂) ef₂
lemma2-1-f✗₂ ef₁ ef₂ m n refl = sr ( sym
        let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
        begin
          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n)) )
        ≡⟨ lem-sr (cr✗ refl) (ef₁ ⊙ (w ^ m) ∙ f✗₂) n s₀ ⟩
          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂) )
        ∎
        )

lemma2-2 : ∀ (ef₁ ef₂ : Fragment spec) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
lemma2-2 ef₁ ef₂ (sr x) = vr (
                         let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
                         begin
                           proj₁ (runFragment s₀ (ef₁ ∙ f))
                         ≡⟨ v=s f (inj₁ refl) ef₁ ⟩
                           proj₂ (runFragment s₀ (ef₁ ∙ f))
                         ≡⟨ x ⟩
                           proj₁ (runFragment s₀ (ef₂ ∙ r))
                         ∎
                         )

lemma2-2-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec) → SR (ef₁ ∙ f✗₂) ef₂ → VR ef₁ (ef₂ ∙ r)
lemma2-2-f✗₂ ef₁ ef₂ (sr x) = vr (
                            let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
                            begin
                              proj₁ (runFragment s₀ ef₁)
                            ≡⟨ x ⟩
                              proj₁ (runFragment s₀ (ef₂ ∙ r))
                            ∎
                            )

lemma2-w✗ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
          → ef₁ ∙ f ⊙ (w ^ m) ∙ w✗ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
          → VR (ef₁ ∙ f) ef₂
lemma2-w✗ ef₁ ef₂ m n refl = let ef₂-r = (ef₁ ∙ f ⊙ (w ^ m) ∙ w✗ ⊙ (r✗ ^ n))
                             in  lemma2-2 ef₁ ef₂-r (lemma2-1 (cw✗ refl) (ef₁ ∙ f) ef₂-r m n refl)

lemma2-f✗₁ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
           → ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₁ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
           → VR (ef₁ ∙ f) ef₂
lemma2-f✗₁ ef₁ ef₂ m n refl = let ef₂-r = (ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₁ ⊙ (r✗ ^ n))
                              in  lemma2-2 ef₁ ef₂-r (lemma2-1 (cf✗₁ refl) (ef₁ ∙ f) ef₂-r m n refl)

lemma2-f✗₂ : ∀ (ef₁ ef₂ : Fragment spec) → ∀ (m n : ℕ)
           → ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n) ∙ r ≡ ef₂
           → VR (ef₁ ∙ f ⊙ (w ^ m)) ef₂
lemma2-f✗₂ ef₁ ef₂ m n refl = let ef₁-new = ef₁ ∙ f ⊙ (w ^ m)
                                  ef₂-r   = ef₁ ∙ f ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n)
                              in  lemma2-2-f✗₂ ef₁-new ef₂-r (lemma2-1-f✗₂ (ef₁ ∙ f) ef₂-r m n refl)

-- lemma2 : ∀ (ef₁ ef₂ : Fragment spec) → ∀ {ac : Action} → Crash₂ ac → ∀ (m n : ℕ)
--        → ef₁ ∙ f ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n) ∙ r ≡ ef₂
--        → VR (ef₁ ∙ f) ef₂
-- lemma2 ef₁ ef₂ (cw✗ x) m n refl = lemma2-w✗ ef₁ ef₂ m n refl
-- lemma2 ef₁ ef₂ (cf✗₁ x) m n refl = lemma2-f✗₁ ef₁ ef₂ m n refl
-- lemma2 ef₁ ef₂ (cf✗₂ x) m n refl = lemma2-f✗₂ ef₁ ef₂ m n refl

------

data RI : Fragment prog → Set
data CI : Fragment prog → Set
data AR : Fragment prog → Fragment spec → Set
data CR : Fragment prog → Fragment spec → Set

data RI where -- Relation Invariance
  ri✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → RI ef → RI (ef ∙ ac)
  ci✓ : {ef : Fragment prog} → CI ef → RI (ef ∙ r)
  id✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → (n : ℕ) → RI ef → RI (ef ⊙ (ac ^ n))
  v✓  : {n : ℕ} → (v : Vec Action n) → All (λ{x → (x ≡ w ⊎ x ≡ f)}) v → RI ⟦ v ⟧v

data CI where -- Crash Invariance
  ri✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → RI ef → CI (ef ∙ ac)
  ci✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → CI ef → CI (ef ∙ ac)
  id✗ : ∀ {ac : Action} → Crash ac → {ef : Fragment prog} → (n : ℕ) → CI ef → CI (ef ⊙ (ac ^ n))

-- Abstract Relation of efp(Fragmant of Prog) and efs(Fragment of Spec)
data AR where
  ar✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f)
      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → AR (efp ∙ ac) (efs ∙ ac)
  cr✓ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → AR (efp ∙ r) (efs ∙ r)
  id✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {efp : Fragment prog} → {efs : Fragment spec}
      → (n : ℕ) → RI efp → AR efp efs → AR (efp ⊙ (ac ^ n)) (efs ⊙ (ac ^ n))
  v✓  : {n : ℕ} → (v : Vec Action n) → All (λ{x → (x ≡ w ⊎ x ≡ f)}) v → AR ⟦ v ⟧v ⟦ v ⟧v

-- Crash Relation
data CR where
  ar✗  : ∀ {ac : Action} → Crash ac
      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → CR (efp ∙ ac) (efs ∙ ac)
  cr✗ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → CR (efp ∙ r✗) (efs ∙ r✗)
  id✗ : ∀ {ac : Action} → Crash ac → {efp : Fragment prog} → {efs : Fragment spec}
      → (n : ℕ) → CI efp → CR efp efs → CR (efp ⊙ (ac ^ n)) (efs ⊙ (ac ^ n))

-- Observational Equivalence -- TODO Is this ok?
data OE : Fragment prog → Fragment spec → Set where
  oe : {efp : Fragment prog} → {efs : Fragment spec} → RI efp × AR efp efs → OE efp efs
--tran : {efp : Fragment prog} → {efs₁ efs₂ : Fragment spec} → VR efs₁ efs₂ → OE efp efs₂ → OE efp efs₁

-- FIXME maybe problematic
data CD : Fragment prog → Fragment prog → Set where
  cd : {efp₁ efp₂ : Fragment prog} → {efs₁ efs₂ : Fragment spec}
     → VR efs₁ efs₂ → OE efp₁ efs₁ → OE efp₂ efs₂ → CD efp₁ efp₂


_✓←✗_ : {a b : Fragment prog} {a' b' : Fragment spec}
      → (CI a → RI b) × (CI a → CR a a' → AR b b') → (CI a × CR a a') → RI b × AR b b'
⟨ g , h ⟩ ✓←✗ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩

_✗←✗_ : {a b : Fragment prog} {a' b' : Fragment spec}
      → (CI a → CI b) × (CI a → CR a a' → CR b b') → (CI a × CR a a') → CI b × CR b b'
⟨ g , h ⟩ ✗←✗ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩

_✗←✓_ : {a b : Fragment prog} {a' b' : Fragment spec}
      → (RI a → CI b) × (RI a → AR a a' → CR b b') → (RI a × AR a a') → CI b × CR b b'
⟨ g , h ⟩ ✗←✓ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩

_✓←✓_ : {a b : Fragment prog} {a' b' : Fragment spec}
      → (RI a → RI b) × (RI a → AR a a' → AR b b') → (RI a × AR a a') → RI b × AR b b'
⟨ g , h ⟩ ✓←✓ ⟨ x , y ⟩ = ⟨ g x , h x y ⟩

lemma1 : ∀ (efp : Fragment prog) → ∀ {ac : Action} → Crash ac → ∀ (i j k : ℕ)
       → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
       → efp ≡ (⟦ v ⟧v) ∙ f ⊙ (w ^ j) ∙ ac ⊙ (r✗ ^ k) ∙ r
       → ∃[ efs ] ( efp <=> efs × (RI efp × AR efp efs) ) -- efs : Fragment spec
lemma1 efp du i j k v all refl = ⟨ red efp , ⟨ redeq refl
                                             , ⟨ ci✓               , cr✓               ⟩
                                           ✓←✗ ⟨ id✗ (cr✗ refl) k  , id✗ (cr✗ refl) k  ⟩
                                           ✗←✗ ⟨ ri✗ du            , ar✗ du            ⟩
                                           ✗←✓ ⟨ id✓ (inj₁ refl) j , id✓ (inj₁ refl) j ⟩
                                           ✓←✓ ⟨ ri✓ (inj₂ refl)   , ar✓ (inj₂ refl)   ⟩
                                           ✓←✓ ⟨ v✓ v all          , v✓ v all          ⟩
                                             ⟩ ⟩

-- theorem : ∀ (efp : Fragment prog)
--         → ∀ {ac : Action} → Crash₂ ac → ∀ (i j k : ℕ)
--         → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
--         → efp ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ ac ⊙ (r✗ ^ k) ∙ r
--         → ∃[ efs ] (OE efp efs)
-- theorem efp (cw✗ x)  i j k v all refl = ⟨ ⟦ v ⟧v ∙ f
--                                         , tran (lemma2-w✗ (⟦ v ⟧v) (red efp) j k refl)
--                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cw✗ x) i j k v all refl)
--                                         ⟩
-- theorem efp (cf✗₁ x) i j k v all refl = ⟨ ⟦ v ⟧v ∙ f
--                                         , tran (lemma2-f✗₁ (⟦ v ⟧v) (red efp) j k refl)
--                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cf✗₁ x) i j k v all refl)
--                                         ⟩
-- theorem efp (cf✗₂ x) i j k v all refl = ⟨ ⟦ v ⟧v ∙ f ⊙ (w ^ j)
--                                         , tran (lemma2-f✗₂ (⟦ v ⟧v) (red efp) j k refl)
--                                                (oe $ proj₂ $ proj₂ $ lemma1 efp (cf✗₂ x) i j k v all refl)
--                                         ⟩

theorem-w✗ : ∀ (efp₁ efp₂ : Fragment prog)
           → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
           → efp₁ ≡ ⟦ v ⟧v ∙ f
           → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ w✗ ⊙ (r✗ ^ k) ∙ r
           → CD efp₁ efp₂
theorem-w✗ efp₁ efp₂ i j k v all refl refl = cd (lemma2-w✗ (⟦ v ⟧v) (red efp₂) j k refl)
                                                (oe (    ⟨ ri✓ (inj₂ refl) , ar✓ (inj₂ refl) ⟩
                                                     ✓←✓ ⟨ v✓ v all        , v✓ v all        ⟩))
                                                (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cw✗ refl) i j k v all refl)

theorem-f✗₁ : ∀ (efp₁ efp₂ : Fragment prog)
            → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
            → efp₁ ≡ ⟦ v ⟧v ∙ f
            → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ f✗₁ ⊙ (r✗ ^ k) ∙ r
            → CD efp₁ efp₂
theorem-f✗₁ efp efp₂ i j k v all refl refl = cd (lemma2-f✗₁ (⟦ v ⟧v) (red efp₂) j k refl)
                                                (oe (    ⟨ ri✓ (inj₂ refl) , ar✓ (inj₂ refl) ⟩
                                                     ✓←✓ ⟨ v✓ v all        , v✓ v all        ⟩))
                                                (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cf✗₁ refl) i j k v all refl)

theorem-f✗₂ : ∀ (efp₁ efp₂ : Fragment prog)
            → ∀ (i j k : ℕ) → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
            → efp₁ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j)
            → efp₂ ≡ ⟦ v ⟧v ∙ f ⊙ (w ^ j) ∙ f✗₂ ⊙ (r✗ ^ k) ∙ r
            → CD efp₁ efp₂
theorem-f✗₂ efp₁ efp₂ i j k v all refl refl = cd (lemma2-f✗₂ (⟦ v ⟧v) (red efp₂) j k refl)
                                                 (oe (    ⟨ id✓ (inj₁ refl) j , id✓ (inj₁ refl) j ⟩
                                                      ✓←✓ ⟨ ri✓ (inj₂ refl)   , ar✓ (inj₂ refl)   ⟩
                                                      ✓←✓ ⟨ v✓ v all          , v✓ v all          ⟩))
                                                 (oe $ proj₂ $ proj₂ $ lemma1 efp₂ (cf✗₂ refl) i j k v all refl)
