module lemma1 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
  
data Snormal : Set where
  w : Snormal → Snormal
  f : Snormal → Snormal
  s0 : Snormal

data Scrash : Set where
  wc : Snormal → Scrash
  fc : Snormal → Scrash

data Sr : Set where
  rc : Sr → Sr
  rcq : Scrash → Sr

data Sfinal : Set where
  r : Sr → Sfinal

data Volatile : Set where
  v : Volatile
  modified : Volatile → Volatile

data Stable : Set where
  s : Stable
  modified : Stable → Stable

data State : Set where
  x : Volatile → Stable → State

data Action : Set where
  w : Action
  f : Action
  r : Action
  wc : Action
  fc : Action
  rc : Action

-- ⟦_⟧p : ∀ (a : Action) → State → State
