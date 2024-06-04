# Directed edges in the booleans

```agda
module simplicial-type-theory.directed-edges-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-booleans
open import foundation.unit-type
open import foundation.universal-property-booleans
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.null-families-of-types
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps

open import simplicial-type-theory.action-on-directed-edges-dependent-functions
open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.dependent-simplicial-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicially-discrete-types
```

</details>

## Idea

We postulate that the [booleans](foundation.booleans.md) are
[simplicially discrete](simplicial-type-theory.simplicially-discrete-types.md)
and hence that all [directed edges](simplicial-type-theory.directed-edges.md)
are constant. This refutes the models of the
[directed interval](simplicial-type-theory.directed-interval.md) in the booleans
and is a differing property between the two types.

As a corollary we have that the universe of simplicially discrete types is
closed under finite coproducts.

## Postulate

```agda
postulate
  is-simplicially-discrete-bool : is-simplicially-discrete bool
```

## Properties

### The booleans are 𝟚-null

```agda
is-𝟚-null-bool : is-null 𝟚 bool
is-𝟚-null-bool =
  is-𝟚-null-is-simplicially-discrete is-simplicially-discrete-bool
```

### The booleans are not a directed interval

```agda
is-not-directed-interval-bool' : 𝟚 ≠ bool
is-not-directed-interval-bool' =
  nonequal-leibniz'
    ( is-simplicially-discrete)
    ( 𝟚)
    ( bool)
    ( is-not-simplicially-discrete-𝟚)
    ( is-simplicially-discrete-bool)

is-not-directed-interval-bool : ¬ (𝟚 ≃ bool)
is-not-directed-interval-bool e =
  is-not-simplicially-discrete-𝟚
    ( is-simplicially-discrete-equiv e is-simplicially-discrete-bool)

is-not-retract-directed-interval-bool : ¬ (𝟚 retract-of bool)
is-not-retract-directed-interval-bool r =
  is-not-simplicially-discrete-𝟚
    ( is-simplicially-discrete-retract r is-simplicially-discrete-bool)
```

### The simplicially discrete types are closed under coproducts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (is-disc-A : is-simplicially-discrete A)
  (is-disc-B : is-simplicially-discrete B)
  where

  abstract
    is-𝟚-null-projection-bool-coproduct :
      is-null-map 𝟚 (projection-bool-coproduct {A = A} {B})
    is-𝟚-null-projection-bool-coproduct =
      is-null-map-left-map-triangle 𝟚
        ( λ where
          (inl _) → refl
          (inr _) → refl)
        ( is-null-map-pr1-is-null-family 𝟚
          ( rec-bool (raise (l1 ⊔ l2) A) (raise (l1 ⊔ l2) B))
          ( λ where
            true →
              is-null-equiv-base
                ( inv-compute-raise (l1 ⊔ l2) A)
                ( is-𝟚-null-is-simplicially-discrete is-disc-A)
            false →
              is-null-equiv-base
                ( inv-compute-raise (l1 ⊔ l2) B)
                ( is-𝟚-null-is-simplicially-discrete is-disc-B)))
        ( is-null-map-map-equiv 𝟚
          ( ( inv-equiv-Σ-bool-coproduct
              ( rec-bool (raise (l1 ⊔ l2) A) (raise (l1 ⊔ l2) B))) ∘e
            ( equiv-coproduct
              ( compute-raise (l1 ⊔ l2) A)
              ( compute-raise (l1 ⊔ l2) B))))

  is-simplicially-discrete-coproduct-Level :
    is-simplicially-discrete A →
    is-simplicially-discrete B →
    is-simplicially-discrete (A + B)
  is-simplicially-discrete-coproduct-Level is-disc-A is-disc-B =
    is-simplicially-discrete-is-𝟚-null
      ( is-null-is-orthogonal-terminal-maps
        ( is-orthogonal-right-comp
          ( terminal-map 𝟚)
          ( projection-bool-coproduct)
          ( terminal-map bool)
          ( is-orthogonal-terminal-maps-is-null is-𝟚-null-bool)
          ( is-orthogonal-terminal-map-is-null-map 𝟚
            ( projection-bool-coproduct)
            ( is-𝟚-null-projection-bool-coproduct))))
```
