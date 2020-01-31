module lemma2 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)

data Action : Set where
  w : Action
  f : Action
  r : Action
  wc : Action
  fc : Action
  rc : Action

data Snormal : Set where
  write : Snormal → w → Snormal
  flush : Snormal → f → Snormal
  s0 : Snormal

data Scrash : Set where
  wc : Snormal → Scrash
  fc : Snormal → Scrash

data Sr : Set where
  rc : Sr → Sr
  rcq : Scrash → Sr

data Sfinal : Set where
  r : Sr → Sfinal

-- data Volatile : Set where
--   volatile : Volatile
--   modified : Volatile → Volatile
-- 
-- data Stable : Set where
--   stable : Stable
--   modified : Stable → Stable
data SubState : Set where
  volatile : SubState
  stable : SubState
  modified : SubState → SubState

data State : Set where
  x : SubState → SubState → State -- Volatile → Stable

⟦_⟧p : Action → State → State
⟦ w ⟧p (x v s) = x (modified v) s
⟦ f ⟧p (x v s) = x v v
⟦ r ⟧p (x v s) = x s s
⟦ wc ⟧p (x v s) = x (modified v) s
⟦ fc ⟧p (x v s) = x (modified v) s
⟦ rc ⟧p (x v s) = x (modified v) s
