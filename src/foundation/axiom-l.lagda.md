#  Axiom L

<details><summary>Imports</summary>
```agda
module foundation.axiom-l where
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-identity-types
open import foundation.universe-levels
```
</details>

## Idea

Axiom L, which is due to Peter Lumsdaine, asserts that for any two types `X` and `Y` in a common universe, the map `X ＝ Y → X ≃ Y` is an embedding. This axiom is a common generalization of the univalence axiom and axiom K, in the sense that both univalence and axiom K imply axiom L.

## Definition

```agda
axiom-L : (l : Level) → UU (lsuc l)
axiom-L l = (X Y : UU l) → is-emb (equiv-eq {A = X} {B = Y})

emb-L : {l : Level} → axiom-L l → (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-L H X Y) = equiv-eq
pr2 (emb-L H X Y) = H X Y
```

## Properties

### Axiom L implies that `Id : A → (A → UU l)` is an embedding

```agda
is-emb-Id : {l : Level} → axiom-L l → (A : UU l) → is-emb (Id {A = A})
is-emb-Id L A x =
  fundamental-theorem-id
    ( pair
      ( pair x refl)
      ( λ u →
        is-injective-emb
          ( emb-fib x)
          ( eq-is-contr (is-contr-total-path x))))
    ( λ y p → ap Id p)
  where
  emb-fib : (x : A) → fib' Id (Id x) ↪ Σ A (λ y → Id x y)
  emb-fib x =
    comp-emb
      ( comp-emb
        ( emb-equiv
          ( equiv-tot
            ( λ y →
              ( equiv-ev-refl y) ∘e
              ( ( equiv-inclusion-is-full-subtype
                  ( λ h →
                    Π-Prop A (λ z → is-equiv-Prop (h z)))
                  ( λ h →
                    fundamental-theorem-id
                      ( is-contr-total-path x)
                      ( h))) ∘e
                ( distributive-Π-Σ)))))
        ( emb-Σ
          ( λ y → (z : A) → Id y z ≃ Id x z)
          ( id-emb)
          ( λ y →
            comp-emb
              ( emb-Π (λ z → emb-L L (Id y z) (Id x z)))
              ( emb-equiv equiv-funext))))
      ( emb-equiv (inv-equiv (equiv-fib Id (Id x))))
```
