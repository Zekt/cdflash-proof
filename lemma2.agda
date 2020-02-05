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
runFragment (ef ∙ ac) = ⟦ ac ⟧p (runFragment ef)

data SR : Fragment → Fragment → Set where -- Stable Reservation
  eq : {ef₁ ef₂ : Fragment} → proj₂ (runFragment ef₁) ≡ proj₂ (runFragment ef₂) → SR ef₁ ef₂

data VR : Fragment → Fragment → Set where -- Volatile Reservation
  eq : {ef₁ ef₂ : Fragment} → proj₁ (runFragment ef₁) ≡ proj₁ (runFragment ef₂) → VR ef₁ ef₂

lem-r : ∀ (ef : Fragment) → proj₁ ( runFragment (ef ∙ r) ) ≡ proj₂ ( runFragment (ef ∙ r) )
lem-r ef = refl

lem-f : ∀ (ef : Fragment) → proj₁ ( runFragment (ef ∙ f) ) ≡ proj₂ ( runFragment (ef ∙ f) )
lem-f ef = refl

--lem : ∀ (ef : Fragment) → proj₁ (runFragment (ef ∙ r)) ≡ proj₂ (runFragment ef)
--lem f' = begin
--           proj₁ ( runFragment (ef ∙ r) )
--         ≡⟨ lem-r ef ⟩
--           proj₂ (runFragment ef)
--         ∎

lemma2-w1 : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ (w ✭) ∙ wc ∙ (rc ✭) ≡ ef₂ → SR ef₁ ef₂
lemma2-w1 ef₁ ef₂ refl = eq refl


lemma2-w2 : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
lemma2-w2 ef₁ ef₂ (eq x) = eq (
                      begin
                        proj₁ (runFragment (ef₁ ∙ f))
                      ≡⟨ lem-f ef₁ ⟩
                        proj₂ (runFragment (ef₁ ∙ f))
                      ≡⟨ x ⟩
                        proj₂ (runFragment ef₂)
                      ≡⟨⟩
                        proj₁ (runFragment (ef₂ ∙ r))
                      ∎
                      )

lemma2-w : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ wc ∙ (rc ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
lemma2-w ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ wc ∙ (rc ✭)) in
                          lemma2-w2 ef₁ ef₂-r (lemma2-w1 (ef₁ ∙ f) ef₂-r refl)
