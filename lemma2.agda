module lemma2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Function using (_∘_)

infixl 20 _∙_

data Action : Set where
  w : Action
  f : Action
  r : Action
  wc : Action
  fc : Action
  rc : Action
  _✭ : Action → Action


data Fragment : Set where
  s0 : Fragment
  _∙_ : Fragment → Action → Fragment

data State : Set where
  vtl0 : State
  stb0 : State
  modified : State → State

⟦_⟧p : Action → State × State → State × State
⟦ w ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
⟦ r ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
⟦ wc ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ fc ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ rc ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ x ✭ ⟧p = ⟦ x ⟧p

runFragment : Fragment → State × State
runFragment s0 = ⟨ vtl0 , stb0 ⟩
runFragment (fg ∙ ac) = ⟦ ac ⟧p (runFragment fg)

data SR : Fragment → Fragment → Set where -- Stable Reservation
  eq : {f₁ f₂ : Fragment} → proj₂ (runFragment f₁) ≡ proj₂ (runFragment f₂) → SR f₁ f₂

data VR : Fragment → Fragment → Set where -- Volatile Reservation
  eq : {f₁ f₂ : Fragment} → proj₁ (runFragment f₁) ≡ proj₁ (runFragment f₂) → VR f₁ f₂

lem-r : ∀ (ef : Fragment) → proj₁ ( runFragment (ef ∙ r) ) ≡ proj₂ ( runFragment (ef ∙ r) )
lem-r ef = refl

lem-f : ∀ (ef : Fragment) → proj₁ ( runFragment (ef ∙ f) ) ≡ proj₂ ( runFragment (ef ∙ f) )
lem-f ef = refl

lem : ∀ (f' : Fragment) → proj₁ (runFragment (f' ∙ r)) ≡ proj₂ (runFragment f')
lem f' = begin
           proj₁ ( runFragment (f' ∙ r) )
         ≡⟨ lem-r f' ⟩
           proj₂ (runFragment f')
         ∎

lemma2-w' : ∀ (f₁ f₂ : Fragment) → f₁ ∙ (w ✭) ∙ wc ∙ (rc ✭) ≡ f₂ → SR f₁ f₂
lemma2-w' f₁ f₂ refl = eq refl


-- lemma2-w : ∀ (f₁ f₂ : Fragment) → SR (f₁ ∙ f) f₂ → VR (f₁ ∙ f) (f₂ ∙ r)
-- lemma2-w f₁ f₂ (eq x) = eq (
--                       begin
--                         proj₁ (runFragment (f₁ ∙ f))
--                       ≡⟨ lem-f f₁ ⟩
--                         proj₂ (runFragment (f₁ ∙ f))
--                       ≡⟨⟩
--                         proj₂ (runFragment f₂)
--                       ≡⟨⟩
--                       ∎
--                       )
