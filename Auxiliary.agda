open import Data.Product
open import Relation.Binary.PropositionalEquality

module Auxiliary (Action : Set) where

TR : Set → Set₁
TR S = S → Action → S → Set

_~_ : Set → Set → Set₁
S ~ T = S → T → Set

Sim : {S T : Set} → TR S → TR T → (S ~ T) → Set
Sim {S} {T} trS trT R = {s s' : S} {t : T} {a : Action} → trS s a s' → R s t → Σ[ t' ∈ T ] (trT t a t' × R s' t')

_∘_ : {S T U : Set} → (S ~ T) → (T ~ U) → (S ~ U)
(R ∘ R') s u = ∃[ t ] (R s t × R' t u)

Sim-trans : {S T U : Set} (trS : TR S) (trT : TR T) (trU : TR U) (R : S ~ T) (R' : T ~ U) →
            Sim trS trT R → Sim trT trU R' → Sim trS trU (R ∘ R')
Sim-trans trS trT trU R R' simST simTU s>s' (t , Rst , R'tu) =
  let (t' , t>t' , Rs't' ) = simST s>s' Rst
      (u' , u>u' , R't'u') = simTU t>t' R'tu
  in  (u' , u>u' , (t' , Rs't' , R't'u'))

_⊗_ : {S T : Set} → TR S → TR T → TR (S × T)
(trS ⊗ trT) (s , t) a (s' , t') = trS s a s' × trT t a t'

lift : {A B : Set} → (A → B) → (A ~ B)
lift f a b = f a ≡ b

simProj₁ : {S T : Set} (trS : TR S) (trT : TR T) → Sim (trS ⊗ trT) trS (lift proj₁)
simProj₁ trS trT (s>s' , t>t') refl = _ , s>s' , refl

lemma : {S T U : Set} (trS : TR S) (trT : TR T) (trU : TR U) (R : S ~ (T × U)) → Sim trS (trT ⊗ trU) R → Sim trS trT (R ∘ lift proj₁)
lemma trS trT trU R sim = Sim-trans trS (trT ⊗ trU) trT R (lift proj₁) sim (simProj₁ trT trU)
