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
  w   :          Action
  f   :          Action
  r   :          Action
  w✗  :          Action
  f✗₁ :          Action
  f✗₂ :          Action
  r✗  :          Action
  _✭  : Action → Action


data Fragment : Set where
  s0  :                     Fragment
  _∙_ : Fragment → Action → Fragment

data State : Set where
  vtl0     :         State
  stb0     :         State
  modified : State → State -- TODO not accurate

⟦_⟧p : Action → State × State → State × State
⟦ w   ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f   ⟧p ⟨ vlt , stb ⟩ = ⟨ vlt , vlt ⟩
⟦ r   ⟧p ⟨ vlt , stb ⟩ = ⟨ stb , stb ⟩
⟦ w✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₁ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ f✗₂ ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , vlt ⟩
⟦ r✗  ⟧p ⟨ vlt , stb ⟩ = ⟨ modified vlt , stb ⟩
⟦ x ✭ ⟧p               = ⟦ x ⟧p -- TODO is this ok?

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

lemma2-1-w✗ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭) ≡ ef₂ → SR ef₁ ef₂
lemma2-1-w✗ ef₁ ef₂ refl = eq refl

lemma2-1-f✗₁ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ (w ✭) ∙ f✗₁ ∙ (r✗ ✭) ≡ ef₂ → SR ef₁ ef₂
lemma2-1-f✗₁ ef₁ ef₂ refl = eq refl

lemma2-1-f✗₂ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ (w ✭) ∙ f✗₂ ∙ (r✗ ✭) ≡ ef₂ → SR (ef₁ ∙ (w ✭) ∙ f✗₂) ef₂
lemma2-1-f✗₂ ef₁ ef₂ refl = eq refl

lemma2-2 : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f) ef₂ → VR (ef₁ ∙ f) (ef₂ ∙ r)
lemma2-2 ef₁ ef₂ (eq x) = eq (
                        begin
                          proj₁ (runFragment (ef₁ ∙ f))
                        ≡⟨ lem-f ef₁ ⟩
                          proj₂ (runFragment (ef₁ ∙ f))
                        ≡⟨ x ⟩
                          proj₁ (runFragment (ef₂ ∙ r))
                        ∎
                        )

lemma2-2-f✗₂ : ∀ (ef₁ ef₂ : Fragment) → SR (ef₁ ∙ f✗₂) ef₂ → VR ef₁ (ef₂ ∙ r)
lemma2-2-f✗₂ ef₁ ef₂ (eq x) = eq (
                            begin
                              proj₁ (runFragment ef₁)
                            ≡⟨ x ⟩
                              proj₁ (runFragment (ef₂ ∙ r))
                            ∎
                            )

lemma2-w✗ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
lemma2-w✗ ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ w✗ ∙ (r✗ ✭)) in
                           lemma2-2 ef₁ ef₂-r (lemma2-1-w✗ (ef₁ ∙ f) ef₂-r refl)

lemma2-f✗₁ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ f✗₁ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f) ef₂
lemma2-f✗₁ ef₁ ef₂ refl = let ef₂-r = (ef₁ ∙ f ∙ (w ✭) ∙ f✗₁ ∙ (r✗ ✭)) in
                            lemma2-2 ef₁ ef₂-r (lemma2-1-f✗₁ (ef₁ ∙ f) ef₂-r refl)

lemma2-f✗₂ : ∀ (ef₁ ef₂ : Fragment) → ef₁ ∙ f ∙ (w ✭) ∙ f✗₂ ∙ (r✗ ✭) ∙ r ≡ ef₂ → VR (ef₁ ∙ f ∙ (w ✭)) ef₂
lemma2-f✗₂ ef₁ ef₂ refl = let ef₁-new = ef₁ ∙ f ∙ (w ✭)
                              ef₂-r   = ef₁ ∙ f ∙ (w ✭) ∙ f✗₂ ∙ (r✗ ✭)
                          in  lemma2-2-f✗₂ ef₁-new ef₂-r (lemma2-1-f✗₂ (ef₁ ∙ f) ef₂-r refl)
