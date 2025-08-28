# Cauchy composition of species of types

```agda
module species.cauchy-composition-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.discrete-relaxed-sigma-decompositions
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.relaxed-sigma-decompositions
open import foundation.trivial-relaxed-sigma-decompositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
open import species.unit-cauchy-composition-species-of-types
```

</details>

## Idea

A [species of types](species.species-of-types.md) `S : UU l1 → UU l2` can be
thought of as the [polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  X ↦ Σ (A : UU l1), (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to
compose species, which is called the
{{#concept "Cauchy composition" Disambiguation="of species of types" Agda=cauchy-composition-species-types}}
of species.

## Definition

### Cauchy composition of species

```agda
cauchy-composition-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → species-types l1 l3 →
  species-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
cauchy-composition-species-types {l1} {l2} {l3} S T X =
  Σ ( Relaxed-Σ-Decomposition l1 l1 X)
    ( λ D →
      ( S (indexing-type-Relaxed-Σ-Decomposition D)) ×
      ( ( y : indexing-type-Relaxed-Σ-Decomposition D) →
        T (cotype-Relaxed-Σ-Decomposition D y)))
```

## Properties

### Unit laws for Cauchy composition of species

```agda
left-unit-law-cauchy-composition-species-types :
  {l1 l2 : Level}
  (F : species-types l1 l2) → (A : UU l1) →
  cauchy-composition-species-types unit-species-types F A ≃ F A
left-unit-law-cauchy-composition-species-types {l1} F A =
  ( left-unit-law-Σ-is-contr
    ( is-contr-type-trivial-Relaxed-Σ-Decomposition)
    ( trivial-Relaxed-Σ-Decomposition l1 A ,
      is-trivial-trivial-Relaxed-Σ-Decomposition {l1} {l1} {A})) ∘e
  ( ( inv-associative-Σ
      ( Relaxed-Σ-Decomposition l1 l1 A)
      ( λ D → is-contr (indexing-type-Relaxed-Σ-Decomposition D))
      ( λ C → F (cotype-Relaxed-Σ-Decomposition (pr1 C) (center (pr2 C))))) ∘e
    ( ( equiv-tot
        ( λ D → equiv-tot (λ C → left-unit-law-Π-is-contr C (center C))))))

right-unit-law-cauchy-composition-species-types :
  {l1 l2 : Level}
  (F : species-types l1 l2) → (A : UU l1) →
  cauchy-composition-species-types F unit-species-types A ≃ F A
right-unit-law-cauchy-composition-species-types {l1} F A =
  ( left-unit-law-Σ-is-contr
    ( is-contr-type-discrete-Relaxed-Σ-Decomposition)
    ( ( discrete-Relaxed-Σ-Decomposition l1 A) ,
      is-discrete-discrete-Relaxed-Σ-Decomposition)) ∘e
  ( ( inv-associative-Σ
      ( Relaxed-Σ-Decomposition l1 l1 A)
      ( λ D →
          ( y : indexing-type-Relaxed-Σ-Decomposition D) →
            is-contr (cotype-Relaxed-Σ-Decomposition D y))
      ( λ D → F (indexing-type-Relaxed-Σ-Decomposition (pr1 D)))) ∘e
    ( ( equiv-tot (λ _ → commutative-product))))
```

### Associativity of composition of species

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2)
  (T : species-types l1 l3)
  (U : species-types l1 l4)
  where

  equiv-associative-cauchy-composition-species-types :
    (A : UU l1) →
    cauchy-composition-species-types
      ( S)
      ( cauchy-composition-species-types T U)
      ( A) ≃
    cauchy-composition-species-types
      ( cauchy-composition-species-types S T)
      ( U)
      ( A)
  equiv-associative-cauchy-composition-species-types A =
    ( equiv-tot
      ( λ D1 →
        ( inv-equiv right-distributive-product-Σ) ∘e
        ( equiv-tot
          ( λ D2 →
            ( inv-associative-Σ
              ( S (indexing-type-Relaxed-Σ-Decomposition D2))
              ( λ _ →
                ( x : indexing-type-Relaxed-Σ-Decomposition D2) →
                T ( cotype-Relaxed-Σ-Decomposition D2 x))
              _))) ∘e
        ( equiv-tot
          ( λ D2 →
            ( equiv-product-right
              ( ( equiv-product-right
                  ( ( inv-equiv
                      ( equiv-precomp-Π
                        ( inv-equiv
                          ( matching-correspondence-Relaxed-Σ-Decomposition
                            D2))
                      ( λ x → U (cotype-Relaxed-Σ-Decomposition D1 x)))) ∘e
                    ( equiv-ind-Σ))) ∘e
                ( distributive-Π-Σ))))))) ∘e
    ( associative-Σ
      ( Relaxed-Σ-Decomposition l1 l1 A)
      ( λ D →
        Relaxed-Σ-Decomposition l1 l1 (indexing-type-Relaxed-Σ-Decomposition D))
      ( _)) ∘e
    ( equiv-Σ-equiv-base _
      ( inv-equiv equiv-displayed-fibered-Relaxed-Σ-Decomposition)) ∘e
    ( inv-associative-Σ
      ( Relaxed-Σ-Decomposition l1 l1 A)
      ( λ D →
        ( x : indexing-type-Relaxed-Σ-Decomposition D) →
          Relaxed-Σ-Decomposition l1 l1 (cotype-Relaxed-Σ-Decomposition D x))
      ( _)) ∘e
    ( equiv-tot
      ( λ D →
        left-distributive-product-Σ ∘e equiv-product-right distributive-Π-Σ))

  htpy-associative-cauchy-composition-species-types :
    cauchy-composition-species-types
      ( S)
      ( cauchy-composition-species-types T U) ~
    cauchy-composition-species-types (cauchy-composition-species-types S T) U
  htpy-associative-cauchy-composition-species-types A =
    eq-equiv (equiv-associative-cauchy-composition-species-types A)

  associative-cauchy-composition-species-types :
    ( cauchy-composition-species-types
      ( S)
      ( cauchy-composition-species-types T U)) ＝
    ( cauchy-composition-species-types (cauchy-composition-species-types S T) U)
  associative-cauchy-composition-species-types =
    eq-htpy htpy-associative-cauchy-composition-species-types
```
