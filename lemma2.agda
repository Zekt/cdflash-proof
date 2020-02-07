module lemma2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)

infixl 20 _∙_
infixl 10 _++_

data Action : Set where
  w   :          Action
  f   :          Action
  r   :          Action
  w✗  :          Action
  f✗₁ :          Action
  f✗₂ :          Action
  r✗  :          Action
--_✭  : Action → Action


data Fragment : Set where
  §_   : Action   →            Fragment
  _∙_  : Fragment → Action   → Fragment
  _++_ : Fragment → Fragment → Fragment
  _^_  : Action → ℕ → Fragment

data State : Set where
  vlt0     :                 State
  stb0     :                 State
  modified : State →         State -- TODO maybe not accurate
  _[_↦_]   : State → ℕ → ℕ → State -- ??

⟦_⟧p : Action → State × State → State × State
⟦ w   ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f   ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
⟦ r   ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
⟦ w✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₁ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₂ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , vlt ⟩
⟦ r✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
-- ⟦ x ✭ ⟧p               = ⟦ x ⟧p -- TODO changed to _^_

runFragment : State × State → Fragment → State × State
runFragment s (§ ac)       = ⟦ ac ⟧p s
runFragment s (ef ∙ ac)    = ⟦ ac ⟧p (runFragment s ef)
runFragment s (ef₁ ++ ef₂) = runFragment (runFragment s ef₁) ef₂
runFragment s (ac ^ zero)  = s
runFragment s (ac ^ suc n) = ⟦ ac ⟧p (runFragment s (ac ^ n))

data SR : Fragment → Fragment → Set where -- Stable Reservation
  eq : {ef₁ ef₂ : Fragment}
     → proj₂ (runFragment ⟨ vlt0 , stb0 ⟩ ef₁) ≡ proj₂ (runFragment ⟨ vlt0 , stb0 ⟩ ef₂)
     → SR ef₁ ef₂

data VR : Fragment → Fragment → Set where -- Volatile Reservation
  eq : {ef₁ ef₂ : Fragment}
     → proj₁ (runFragment ⟨ vlt0 , stb0 ⟩ ef₁) ≡ proj₁ (runFragment ⟨ vlt0 , stb0 ⟩ ef₂)
     → VR ef₁ ef₂
 
lem-r : ∀ (ef : Fragment)
      → proj₁ ( runFragment ⟨ vlt0 , stb0 ⟩ (ef ∙ r) ) ≡ proj₂ ( runFragment ⟨ vlt0 , stb0 ⟩ (ef ∙ r) )
lem-r ef = refl
 
lem-f : ∀ (ef : Fragment)
      → proj₁ ( runFragment ⟨ vlt0 , stb0 ⟩ (ef ∙ f) ) ≡ proj₂ ( runFragment ⟨ vlt0 , stb0 ⟩ (ef ∙ f) )
lem-f ef = refl

lem-++ : ∀ (ef₁ ef₂ : Fragment)
       → ( ∀ (s : State × State) → proj₂ (runFragment s ef₂) ≡ proj₂ s )
       → ∀ (t : State × State) → proj₂ (runFragment t (ef₁ ++ ef₂)) ≡ proj₂ (runFragment t ef₁)
lem-++ ef₁ ef₂ lem t = begin
                         proj₂ (runFragment t (ef₁ ++ ef₂))
                       ≡⟨⟩
                       -- s ≡ t → (runFragment _ ef₂) s = (runFragment _ ef₂) t
                         proj₂ (runFragment (runFragment t ef₁) ef₂)
                       ≡⟨ lem (runFragment t ef₁) ⟩
                         proj₂ (runFragment t ef₁)
                       ∎

lem-r✗✭-1 : ∀ (n : ℕ) → ∀ (s : State × State) → proj₂ (runFragment s (r✗ ^ n)) ≡ proj₂ s
lem-r✗✭-1 zero s = refl
lem-r✗✭-1 (suc n) s = lem-r✗✭-1 n s

lem-w✭-1 : ∀ (n : ℕ) → ∀ (s : State × State) → proj₂ (runFragment s (w ^ n)) ≡ proj₂ s
lem-w✭-1 zero s = refl
lem-w✭-1 (suc n) s = lem-w✭-1 n s

lem-r✗✭ : ∀ (ef : Fragment) → ∀ (n : ℕ)
        → ∀ (s : State × State) → proj₂ ( runFragment s (ef ++ (r✗ ^ n)) ) ≡ proj₂ ( runFragment s ef )
lem-r✗✭ ef n s = begin
                   proj₂ ( runFragment s (ef ++ (r✗ ^ n)) )
                 ≡⟨ lem-++ ef (r✗ ^ n) (lem-r✗✭-1 n) s ⟩
                   proj₂ ( runFragment s ef )
                 ∎

lem-w✭ : ∀ (ef : Fragment) → ∀ (n : ℕ)
       → ∀ (s : State × State) → proj₂ ( runFragment s (ef ++ (w ^ n)) ) ≡ proj₂ ( runFragment s ef )
lem-w✭ ef n s = begin
                 proj₂ ( runFragment s (ef ++ (w ^ n)) )
               ≡⟨ lem-++ ef (w ^ n) (lem-w✭-1 n) s ⟩
                 proj₂ ( runFragment s ef )
               ∎

lemma2-1-w✗ : ∀ (ef₁ ef₂ : Fragment)
            → ∀ (m n : ℕ) → ef₁ ++ (w ^ m) ∙ w✗ ++ (r✗ ^ n) ≡ ef₂
            → SR ef₁ ef₂
lemma2-1-w✗ ef₁ ef₂ m n refl = eq ( sym
       let s₀ = ⟨ vlt0 , stb0 ⟩ in
       begin 
         proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ w✗ ++ (r✗ ^ n)) )
       ≡⟨ lem-r✗✭ (ef₁ ++ (w ^ m) ∙ w✗) n s₀ ⟩
         proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ w✗) )
       ≡⟨ lem-w✭ ef₁ m s₀ ⟩
         proj₂ (runFragment s₀ ef₁)
       ∎
    )

lemma2-1-f✗₁ : ∀ (ef₁ ef₂ : Fragment)
            → ∀ (m n : ℕ) → ef₁ ++ (w ^ m) ∙ f✗₁ ++ (r✗ ^ n) ≡ ef₂
            → SR ef₁ ef₂
lemma2-1-f✗₁ ef₁ ef₂ m n refl = eq ( sym
        let s₀ = ⟨ vlt0 , stb0 ⟩ in
        begin 
          proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ f✗₁ ++ (r✗ ^ n)) )
        ≡⟨ lem-r✗✭ (ef₁ ++ (w ^ m) ∙ w✗) n s₀ ⟩
          proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ f✗₁) )
        ≡⟨ lem-w✭ ef₁ m s₀ ⟩
          proj₂ (runFragment s₀ ef₁)
        ∎
     )

-- lemma2-1-f✗₂ : ∀ (ef₁ ef₂ : Fragment)
--              → ∀ (m n : ℕ) → ef₁ ∙ (w ^ m) ∙ f✗₂ ∙ (r✗ ^ n) ≡ ef₂
--              → SR (ef₁ ∙ (w ^ m) ∙ f✗₂) ef₂
-- lemma2-1-f✗₂ ef₁ ef₂ m n refl = eq ( sym
--         let s₀ = ⟨ vlt0 , stb0 ⟩ in
--         begin 
--           proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ f✗₂ ++ (r✗ ^ n)) )
--         ≡⟨ lem-r✗✭ (ef₁ ++ (w ^ m) ∙ w✗) n s₀ ⟩
--           proj₂ ( runFragment s₀ (ef₁ ++ (w ^ m) ∙ f✗₂) )
--         ≡⟨ lem-w✭ ef₁ m s₀ ⟩
--           proj₂ (runFragment s₀ ef₁)
--         ∎
--      )

-- lemma2-2 : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
-- lemma2-2 ef₁ ef₂ (eq x) = eq (
--                         begin
--                           proj₁ (runFragment (ef₁ ∙ f))
--                         ≡⟨ lem-f ef₁ ⟩
--                           proj₂ (runFragment (ef₁ ∙ f))
--                         ≡⟨ x ⟩
--                           proj₁ (runFragment (ef₂ ∙ r))
--                         ∎
--                         )
-- 
-- lemma2-2-f✗₂ : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f✗₂) ef₂ → VR ef₁ (ef₂ ∙ r)
-- lemma2-2-f✗₂ ef₁ ef₂ (eq x) = eq (
--                             begin
--                               proj₁ (runFragment ef₁)
--                             ≡⟨ x ⟩
--                               proj₁ (runFragment (ef₂ ∙ r))
--                             ∎
--                             )
-- 
-- 
-- -- lemma2-w✗ : ∀ (ef₁ ef₂ : Fragment) → ∀ (m n : ℕ) → ef₁ ∙ f ∙ (w ^ m) ∙ w✗ ∙ (r✗ ^ n) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
-- -- lemma2-w✗ ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭)) in
-- --                            lemma2-2 ef₁ ef₂-r (lemma2-1-w✗ (ef₁ ∙ f) ef₂-r refl)
-- 
-- lemma2-f✗₁ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ f✗₁ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
-- lemma2-f✗₁ ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ f✗₁ ∙ (r✗ ✭)) in
--                             lemma2-2 ef₁ ef₂-r (lemma2-1-f✗₁ (ef₁ ∙ f) ef₂-r refl)
-- 
-- lemma2-f✗₂ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ f✗₂ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f ∙ (w ✭)) ef₂
-- lemma2-f✗₂ ef₁ ef₂ refl = let ef₁-new = ef₁ ∙ f ∙ (w ✭)
--                               ef₂-r   = ef₁ ∙ f ∙ (w ✭) ∙ f✗₂ ∙ (r✗ ✭)
--                           in  lemma2-2-f✗₂ ef₁-new ef₂-r (lemma2-1-f✗₂ (ef₁ ∙ f) ef₂-r refl)
-- 
-- -- data RI (ef : Fragment) : Set where
-- --  : RI ef → RI (ef ∙ w)
-- --  : RI ef → RI (ef ∙ f)
-- --  : CI ef → RI (ef ∙ r)
-- -- 
-- -- data CI (ef : Fragment) : Set where
-- --  : RI ef → CI (ef ∙ w✗)
-- --  : RI ef → CI (ef ∙ f✗)
-- --  : CI ef → CI (ef ∙ f✗)
