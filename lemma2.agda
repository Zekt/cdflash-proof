module lemma2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (¬_)

infixl 20 _∙_

data Action : Set where
  w : Action
  f : Action
  r : Action
  w✗ : Action
  f✗ : Action
  r✗ : Action
  _✭ : Action → Action


data Fragment : Set where
  s0 : Fragment
  _∙_ : Fragment → Action → Fragment

data State : Set where
  vtl0 : State
  stb0 : State
  crashed : State → State

⟦_⟧p : Action → List (State × State) → List (State × State)
⟦ _ ⟧p [] = []
⟦ w ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ crashed vlt , stb ⟩ ∷ ⟦ w ⟧p ss
⟦ f ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ vlt , vlt ⟩ ∷ ⟦ f ⟧p ss
⟦ r ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ stb , stb ⟩ ∷ ⟦ r ⟧p ss
⟦ w✗ ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ crashed vlt , stb ⟩ ∷ ⟦ w✗ ⟧p ss
⟦ f✗ ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ crashed vlt , stb ⟩ ∷ (⟨ crashed vlt , vlt ⟩ ∷ ⟦ w✗ ⟧p ss)
⟦ r✗ ⟧p ( ⟨ vlt , stb ⟩ ∷ ss ) = ⟨ crashed vlt , stb ⟩ ∷ ⟦ r✗ ⟧p ss
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

lemma2-w₁ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭) ≡ ef₂ → SR ef₁ ef₂
lemma2-w₁ ef₁ ef₂ refl = eq refl


lemma2-w₂ : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
lemma2-w₂ ef₁ ef₂ (eq x) = eq (
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

lemma2-w : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
lemma2-w ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭)) in
                          lemma2-w₂ ef₁ ef₂-r (lemma2-w₁ (ef₁ ∙ f) ef₂-r refl)

-- lemma2-f : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ f✗ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
