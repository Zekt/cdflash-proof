module lemma2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec

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

data Ft : Set where
  prog : Ft
  spec : Ft

data Fragment (t : Ft) : Set where
  §_   : Action     →                Fragment t
  _∙_  : Fragment t → Action       → Fragment t
  _⊙_  : Fragment t → Fragment t   → Fragment t
  _^_  : Action     → ℕ            → Fragment t
  ⟦_⟧v : {n : ℕ}    → Vec Action n → Fragment t

red : {s t : Ft} → Fragment s → Fragment t
red (§ x)      = § x
red (ff ∙ x)   = red ff ∙ x
red (ff ⊙ ff₁) = red ff ⊙ red ff₁
red (x ^ n)    = x ^ n
red ⟦ xs ⟧v    = ⟦ xs ⟧v

data _<=>_ (a : Fragment prog) (b : Fragment spec) : Set where
  redeq : red a ≡ b → a <=> b

data State : Set where
  vlt₀     :                 State
  stb₀     :                 State
  modified : State →         State -- TODO maybe not accurate
  _[_↦_]   : State → ℕ → ℕ → State -- ??

-- data _⟦_⟧▸_ : State × State → Action → State × State → Set where
--    _w▸_ : (a b : State × State) → proj₂ a ≡ proj₂ b → a ⟦ w ⟧▸ b
--    _f▸_ : (a b : State × State) → ⟨ proj₁ a ≡ proj₁ b , proj₁ a ≡ proj₂ b ⟩ → a ⟦ f ⟧▸ b

⟦_⟧p : Action → State × State → State × State
⟦ w   ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f   ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
⟦ r   ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
⟦ w✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₁ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₂ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , vlt ⟩
⟦ r✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩

runFragment : State × State → Fragment spec → State × State
runFragment s (§ ac)       = ⟦ ac ⟧p s
runFragment s (ef ∙ ac)    = ⟦ ac ⟧p (runFragment s ef)
runFragment s (ef₁ ⊙ ef₂)  = runFragment (runFragment s ef₁) ef₂
runFragment s (ac ^ zero)  = s
runFragment s (ac ^ suc n) = ⟦ ac ⟧p (runFragment s (ac ^ n))
runFragment s ⟦ [] ⟧v      = s
runFragment s ⟦ x ∷ xs ⟧v  = runFragment (⟦ x ⟧p s) ⟦ xs ⟧v

data SR : Fragment spec → Fragment spec → Set where -- Stable Reservation
  eq : {ef₁ ef₂ : Fragment spec}
     → proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₁) ≡ proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₂)
     → SR ef₁ ef₂

data VR : Fragment spec → Fragment spec → Set where -- Volatile Reservation
  eq : {ef₁ ef₂ : Fragment spec}
     → proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₁) ≡ proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ ef₂)
     → VR ef₁ ef₂

v=s : ∀ (ac : Action) → (ac ≡ f ⊎ ac ≡ r) → ∀ (ef : Fragment spec)
    → proj₁ (runFragment ⟨ vlt₀ , stb₀ ⟩ (ef ∙ ac)) ≡ proj₂ (runFragment ⟨ vlt₀ , stb₀ ⟩ (ef ∙ ac))
v=s f (inj₁ x) ef = refl
v=s r (inj₂ y) ef = refl


lem-⊙ : ∀ (ef₁ ef₂ : Fragment spec)
       → ( ∀ (s : State × State) → proj₂ (runFragment s ef₂) ≡ proj₂ s )
       → ∀ (t : State × State) → proj₂ (runFragment t (ef₁ ⊙ ef₂)) ≡ proj₂ (runFragment t ef₁)
lem-⊙ ef₁ ef₂ lem t = begin
                        proj₂ (runFragment t (ef₁ ⊙ ef₂))
                      ≡⟨ lem (runFragment t ef₁) ⟩
                        proj₂ (runFragment t ef₁)
                      ∎

data Du : Action → Set where -- disjoint union of stable reserving actions
  cw   : {ac : Action} → ac ≡ w   → Du w
  cr   : {ac : Action} → ac ≡ r   → Du r
  cw✗  : {ac : Action} → ac ≡ w✗  → Du w✗
  cf✗₁ : {ac : Action} → ac ≡ f✗₁ → Du f✗₁
  cr✗  : {ac : Action} → ac ≡ r✗  → Du r✗


s^n=s : ∀ {ac : Action} → Du ac
      → ∀ (n : ℕ) → ∀ (s : State × State) → proj₂ (runFragment s (ac ^ n)) ≡ proj₂ s
s^n=s {ac}   du       zero    s = refl
s^n=s {.w}   (cw x)   (suc n) s = s^n=s (cw x)   n s
s^n=s {.r}   (cr x)   (suc n) s = s^n=s (cr x)   n s
s^n=s {.w✗}  (cw✗ x)  (suc n) s = s^n=s (cw✗ x)  n s
s^n=s {.f✗₁} (cf✗₁ x) (suc n) s = s^n=s (cf✗₁ x) n s
s^n=s {.r✗}  (cr✗ x)  (suc n) s = s^n=s (cr✗ x)  n s

lem-sr : ∀ {ac : Action} → Du ac → ∀ (ef : Fragment spec) → ∀ (n : ℕ)
        → ∀ (s : State × State) → proj₂ ( runFragment s (ef ⊙ (ac ^ n)) ) ≡ proj₂ ( runFragment s ef )
lem-sr {ac} du ef n s = begin
                    proj₂ ( runFragment s (ef ⊙ (ac ^ n)) )
                  ≡⟨ lem-⊙ ef (ac ^ n) (s^n=s du n) s ⟩
                    proj₂ ( runFragment s ef )
                  ∎

lemma2-1 : ∀ {ac : Action} → Du ac
         → ∀ (ef₁ ef₂ : Fragment spec)
         → ∀ (m n : ℕ) → ef₁ ⊙ (w ^ m) ∙ ac ⊙ (r✗ ^ n) ≡ ef₂
         → SR ef₁ ef₂
lemma2-1 {ac} du ef₁ ef₂ m n refl = eq ( sym
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
             → SR (ef₁ ⊙ (w ^ m) ∙ f✗₂) ef₂
lemma2-1-f✗₂ ef₁ ef₂ m n refl = eq ( sym
        let s₀ = ⟨ vlt₀ , stb₀ ⟩ in
        begin
          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂ ⊙ (r✗ ^ n)) )
        ≡⟨ lem-sr (cr✗ refl) (ef₁ ⊙ (w ^ m) ∙ f✗₂) n s₀ ⟩
          proj₂ ( runFragment s₀ (ef₁ ⊙ (w ^ m) ∙ f✗₂) )
        ∎
        )

lemma2-2 : ∀ (ef₁ ef₂ : Fragment spec) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
lemma2-2 ef₁ ef₂ (eq x) = eq (
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
lemma2-2-f✗₂ ef₁ ef₂ (eq x) = eq (
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

------

data Du✓ : Action → Set where -- disjoint union of success functions
  cw : {ac : Action} → ac ≡ w → Du✓ w
  cf : {ac : Action} → ac ≡ f → Du✓ f
  cr : {ac : Action} → ac ≡ r → Du✓ r

data Du✗ : Action → Set where -- disjoint union of crash functions
  cw✗  : {ac : Action} → ac ≡ w✗  → Du✗ w✗
  cf✗₁ : {ac : Action} → ac ≡ f✗₁ → Du✗ f✗₁
  cf✗₂ : {ac : Action} → ac ≡ f✗₂ → Du✗ f✗₂
  cr✗  : {ac : Action} → ac ≡ r✗  → Du✗ r✗

data RI : Fragment prog → Set
data CI : Fragment prog → Set
data AR : Fragment prog → Fragment spec → Set
data CR : Fragment prog → Fragment spec → Set

data RI where
  ri✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → RI ef → RI (ef ∙ ac)
  ci✓ : {ef : Fragment prog} → CI ef → RI (ef ∙ r)
  id✓ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f) → {ef : Fragment prog} → (n : ℕ) → RI ef → RI (ef ⊙ (ac ^ n))
  v✓  : {n : ℕ} → (v : Vec Action n) → All (λ{x → (x ≡ w ⊎ x ≡ f)}) v → RI ⟦ v ⟧v

data CI where
  ri✗ : ∀ {ac : Action} → Du✗ ac → {ef : Fragment prog} → RI ef → CI (ef ∙ ac)
  ci✗ : ∀ {ac : Action} → Du✗ ac → {ef : Fragment prog} → CI ef → CI (ef ∙ ac)
  id✗ : ∀ {ac : Action} → Du✗ ac → {ef : Fragment prog} → (n : ℕ) → CI ef → CI (ef ⊙ (ac ^ n))

-- Abstract Relation of efp(Fragmant of Prog) and efs(Fragment of Spec)
data AR where
  ar→ : ∀ {ac : Action} → (ac ≡ w ⊎ ac ≡ f)
      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → AR (efp ∙ ac) (efs ∙ ac)
  cr→ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → AR (efp ∙ r) (efs ∙ r)

-- Crash Relation
data CR where
  ar→  : ∀ {ac : Action} → Du✗ ac
      → {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → CR (efp ∙ ac) (efs ∙ ac)
  cr→ : {efp : Fragment prog} → {efs : Fragment spec} → CI efp → CR efp efs → CR (efp ∙ r✗) (efs ∙ r✗)

-- Observational Equivalence
data OE : Fragment prog → Fragment spec → Set where
  conclude : {efp : Fragment prog} → {efs : Fragment spec} → RI efp → AR efp efs → OE efp efs
-- test : {efp : Fragment prog} → {efs : Fragment spec} → efp <=> efs → OE efp efs

-- Simulation Relation
-- SR : Fragment → Fragment → Set where

-- data _==_ : Fragment t → Fragment t → Set
  
-- ext : (efp : Fragment prog)
--     → {ef : Fragment prog} {ac : Action} {n : ℕ} → efp ≡ ef ⊙ (ac ^ n)
--     → Fragment prog
-- ext (efp ⊙ (ac ^ zero)) refl = efp
-- ext (efp ⊙ (ac ^ (suc n))) refl = efp ⊙ (ac ^ n) ∙ ac

_✓←✗_ : {a b : Fragment prog} → (CI a → RI b) → CI a → RI b
g ✓←✗ x = g x

_✗←✗_ : {a b : Fragment prog} → (CI a → CI b) → CI a → CI b
g ✗←✗ x = g x

_✗←✓_ : {a b : Fragment prog} → (RI a → CI b) → RI a → CI b
g ✗←✓ x = g x

_✓←✓_ : {a b : Fragment prog} → (RI a → RI b) → RI a → RI b
g ✓←✓ x = g x

lemma-1 : ∀ (efp : Fragment prog) → ∀ {ac : Action} → Du✗ ac → ∀ (i j k : ℕ)
        → ∀ (v : Vec Action i) → All (λ{x → x ≡ w ⊎ x ≡ f}) v
        → efp ≡ (⟦ v ⟧v) ∙ f ⊙ (w ^ j) ∙ ac ⊙ (r✗ ^ k) ∙ r
        → ∃[ efs ] ( efp <=> efs × (RI efp × AR efp efs) )
lemma-1 efp du i j k v all refl = ⟨ red efp , ⟨ redeq refl , ⟨ ci✓
                                                           ✓←✗ id✗ (cr✗ refl) k
                                                           ✗←✗ ri✗ du
                                                           ✗←✓ id✓ (inj₁ refl) j
                                                           ✓←✓ ri✓ (inj₂ refl)
                                                           ✓←✓ v✓ v all
                                                             , {! !}
                                                             ⟩ ⟩ ⟩

-- theorem : ∀ (efp ef : Fragment) → (efp ≡ ef ∙ f) → OE efp ef
