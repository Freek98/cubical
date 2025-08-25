{-

This file introduces the "powerset" of a type in the style of
Escardó's lecture notes:

https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#propositionalextensionality

-}
module Cubical.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

ℙ : Type ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
ℙ X ℓ' = X → hProp ℓ'

isSetℙ : {ℓ' : Level} → isSet (ℙ X ℓ')
isSetℙ = isSetΠ λ x → isSetHProp

infix 5 _∈_

_∈_ : {X : Type ℓ} → X → ℙ X ℓ' → Type ℓ'
x ∈ A = ⟨ A x ⟩

_⊆_ : {X : Type ℓ} → ℙ X ℓ' → ℙ X ℓ' → Type _
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-isProp : (A : ℙ X ℓ') (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

⊆-isProp : (A B : ℙ X ℓ') → isProp (A ⊆ B)
⊆-isProp A B = isPropΠ2 (λ x _ → ∈-isProp B x)

⊆-refl : (A : ℙ X ℓ') → A ⊆ A
⊆-refl A x = idfun (x ∈ A)

subst-∈ : (A : ℙ X ℓ') {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

⊆-refl-consequence : (A B : ℙ X ℓ') → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : ℙ X ℓ') → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) (φ x) (ψ x)))

⊆-trans : (A B C : ℙ X ℓ') → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A B C φ ψ x = ψ x ∘ φ x

⊆-antisym : (A B : ℙ X ℓ') → A ⊆ B → B ⊆ A → A ≡ B
⊆-antisym A B φ ψ = ⊆-extensionality A B (φ , ψ)

⊆-extensionalityEquiv : (A B : ℙ X ℓ') → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSetℙ A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))
