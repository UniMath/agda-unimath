# Null types

```agda
module orthogonal-factorization-systems.null-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.postcomposition-dependent-functions
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.type-arithmetic-unit-type
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.maps-local-at-maps
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

A type `A` is said to be
{{#concept "null at" Disambiguation="type" Agda=is-null}} `Y`, or
{{#concept "`Y`-null" Disambiguation="type" Agda=is-null}}, if the
[diagonal map](foundation.diagonal-maps-of-types.md)

```text
  Δ : A → (Y → A)
```

is an [equivalence](foundation-core.equivalences.md). The idea is that `A`
"observes" the type `Y` to be
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate on a type of being `Y`-null

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-null : UU (l1 ⊔ l2)
  is-null = is-equiv (diagonal-exponential A Y)

  is-prop-is-null : is-prop is-null
  is-prop-is-null = is-property-is-equiv (diagonal-exponential A Y)

  is-null-Prop : Prop (l1 ⊔ l2)
  pr1 is-null-Prop = is-null
  pr2 is-null-Prop = is-prop-is-null
```

## Properties

### Closure under equivalences

If `B` is `Y`-null and we have equivalences `X ≃ Y` and `A ≃ B`, then `A` is
`X`-null.

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4}
  where

  is-null-equiv : (e : X ≃ Y) (f : A ≃ B) → is-null Y B → is-null X A
  is-null-equiv e f H =
    is-equiv-htpy-equiv
      ( equiv-precomp e A ∘e equiv-postcomp Y (inv-equiv f) ∘e (_ , H) ∘e f)
      ( λ x → eq-htpy (λ _ → inv (is-retraction-map-inv-equiv f x)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {A : UU l3}
  where

  is-null-equiv-exponent : (e : X ≃ Y) → is-null Y A → is-null X A
  is-null-equiv-exponent e H =
    is-equiv-comp
      ( precomp (map-equiv e) A)
      ( diagonal-exponential A Y)
      ( H)
      ( is-equiv-precomp-equiv e A)

module _
  {l1 l2 l3 : Level} {Y : UU l1} {A : UU l2} {B : UU l3}
  where

  is-null-equiv-base : (f : A ≃ B) → is-null Y B → is-null Y A
  is-null-equiv-base f H =
    is-equiv-htpy-equiv
      ( equiv-postcomp Y (inv-equiv f) ∘e (_ , H) ∘e f)
      ( λ b → eq-htpy (λ _ → inv (is-retraction-map-inv-equiv f b)))
```

### Closure under retracts

If `B` is `Y`-null and `X` is a retract of `Y` and `A` is a retract of `B`, then
`A` is `X`-null.

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4}
  where

  is-null-retract :
    X retract-of Y → A retract-of B → is-null Y B → is-null X A
  is-null-retract e f =
    is-equiv-retract-map-is-equiv
      ( diagonal-exponential A X)
      ( diagonal-exponential B Y)
      ( retract-map-diagonal-exponential-retract f e)

module _
  {l1 l2 l3 : Level} {Y : UU l1} {A : UU l2} {B : UU l3}
  where

  is-null-retract-base : A retract-of B → is-null Y B → is-null Y A
  is-null-retract-base = is-null-retract id-retract

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {A : UU l3}
  where

  is-null-retract-exponent : X retract-of Y → is-null Y A → is-null X A
  is-null-retract-exponent e = is-null-retract e id-retract
```

### A type is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1 l2 : Level} (Y : UU l1) (A : UU l2)
  where

  is-local-terminal-map-is-null : is-null Y A → is-local (terminal-map Y) A
  is-local-terminal-map-is-null =
    is-equiv-comp
      ( diagonal-exponential A Y)
      ( map-left-unit-law-function-type A)
      ( is-equiv-map-left-unit-law-function-type A)

  is-null-is-local-terminal-map : is-local (terminal-map Y) A → is-null Y A
  is-null-is-local-terminal-map =
    is-equiv-comp
      ( precomp (terminal-map Y) A)
      ( map-inv-left-unit-law-function-type A)
      ( is-equiv-map-inv-left-unit-law-function-type A)

  equiv-is-local-terminal-map-is-null :
    is-null Y A ≃ is-local (terminal-map Y) A
  equiv-is-local-terminal-map-is-null =
    equiv-iff-is-prop
      ( is-property-is-equiv (diagonal-exponential A Y))
      ( is-property-is-equiv (precomp (terminal-map Y) A))
      ( is-local-terminal-map-is-null)
      ( is-null-is-local-terminal-map)

  equiv-is-null-is-local-terminal-map :
    is-local (terminal-map Y) A ≃ is-null Y A
  equiv-is-null-is-local-terminal-map =
    inv-equiv equiv-is-local-terminal-map-is-null
```

### A type is `Y`-null if and only if the terminal projection of `Y` is orthogonal to the terminal projection of `A`

```agda
module _
  {l1 l2 : Level} {Y : UU l1} {A : UU l2}
  where

  is-null-is-orthogonal-terminal-maps :
    is-orthogonal (terminal-map Y) (terminal-map A) → is-null Y A
  is-null-is-orthogonal-terminal-maps H =
    is-null-is-local-terminal-map Y A
      ( is-local-is-orthogonal-terminal-map (terminal-map Y) H)

  is-orthogonal-terminal-maps-is-null :
    is-null Y A → is-orthogonal (terminal-map Y) (terminal-map A)
  is-orthogonal-terminal-maps-is-null H =
    is-orthogonal-is-orthogonal-fiber-condition-right-map
      ( terminal-map Y)
      ( terminal-map A)
      ( λ _ →
        is-equiv-source-is-equiv-target-equiv-arrow
          ( precomp (terminal-map Y) (fiber (terminal-map A) star))
          ( diagonal-exponential A Y)
          ( ( equiv-fiber-terminal-map star) ∘e
            ( equiv-universal-property-unit (fiber (terminal-map A) star)) ,
            ( equiv-postcomp Y (equiv-fiber-terminal-map star)) ,
            ( refl-htpy))
          ( H))
```

### A type is `f`-local if it is null at every fiber of `f`

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {X : UU l2} (f : Y → X)
  where

  is-local-dependent-type-is-null-fiber :
    (A : X → UU l3) →
    ((x : X) → is-null (fiber f x) (A x)) → is-local-dependent-type f A
  is-local-dependent-type-is-null-fiber A = is-equiv-precomp-Π-fiber-condition

  is-local-is-null-fiber :
    (A : UU l3) → ((x : X) → is-null (fiber f x) A) → is-local f A
  is-local-is-null-fiber A = is-local-dependent-type-is-null-fiber (λ _ → A)
```

### Null types are closed under dependent sums

This is Theorem 2.19 in {{#cite RSS20}}.

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {A : UU l2} {B : A → UU l3}
  (is-null-A : is-null Y A)
  (is-null-B : (x : A) → is-null Y (B x))
  where

  is-null-Σ : is-null Y (Σ A B)
  is-null-Σ =
    is-equiv-map-equiv
      ( equivalence-reasoning
        Σ A B
        ≃ Σ (Y → A) (λ f → (x : Y) → B (f x))
        by
          equiv-Σ
            ( λ f → (x : Y) → B (f x))
            ( diagonal-exponential A Y , is-null-A)
            ( λ x → diagonal-exponential (B x) Y , is-null-B x)
        ≃ (Y → Σ A B)
        by inv-distributive-Π-Σ)
```

### Contractible types are null at all types

```agda
is-null-is-contr :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) → is-contr A → is-null B A
is-null-is-contr {A = A} B is-contr-A =
  is-null-is-local-terminal-map B A
    ( is-local-is-contr (terminal-map B) A is-contr-A)
```

### Propositions are null at inhabited types

```agda
module _
  {l1 l2 : Level} {Y : UU l1}
  where

  is-null-is-prop-is-inhabited' :
    {P : UU l2} → Y → is-prop P → is-null Y P
  is-null-is-prop-is-inhabited' {P} y is-prop-P =
    is-equiv-has-converse-is-prop
      ( is-prop-P)
      ( is-prop-function-type is-prop-P)
      ( λ f → f y)

  is-null-is-prop-is-inhabited :
    {P : UU l2} → is-inhabited Y → is-prop P → is-null Y P
  is-null-is-prop-is-inhabited {P} is-inhabited-Y is-prop-P =
    is-equiv-has-converse-is-prop
      ( is-prop-P)
      ( is-prop-function-type is-prop-P)
      ( λ f → rec-trunc-Prop (P , is-prop-P) f is-inhabited-Y)

  is-null-prop-is-inhabited :
    is-inhabited Y → (P : Prop l2) → is-null Y (type-Prop P)
  is-null-prop-is-inhabited is-inhabited-Y P =
    is-null-is-prop-is-inhabited is-inhabited-Y (is-prop-type-Prop P)
```

### Null types are closed under dependent products

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {I : UU l2} {B : I → UU l3}
  where

  abstract
    is-null-Π : ((i : I) → is-null Y (B i)) → is-null Y ((i : I) → B i)
    is-null-Π is-null-B =
      is-null-is-orthogonal-terminal-maps
        ( is-orthogonal-right-comp
          ( terminal-map Y)
          ( postcomp-Π I (λ {i : I} → terminal-map (B i)))
          ( terminal-map (I → unit))
          ( is-orthogonal-is-equiv-right
            ( terminal-map Y)
            ( terminal-map (I → unit))
            ( is-equiv-terminal-map-Π-unit))
          ( is-orthogonal-right-Π
            ( terminal-map Y)
            ( λ i → terminal-map (B i))
            ( λ i → (is-orthogonal-terminal-maps-is-null (is-null-B i)))))
```

### Null types are closed under exponentiation

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {I : UU l2} {B : UU l3}
  where

  is-null-function-type : is-null Y B → is-null Y (I → B)
  is-null-function-type is-null-B = is-null-Π (λ _ → is-null-B)
```

### Null types are closed under cartesian products

```agda
module _
  {l1 l2 l3 : Level} {Y : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-null-product : is-null Y A → is-null Y B → is-null Y (A × B)
    is-null-product is-null-A is-null-B =
      is-null-is-orthogonal-terminal-maps
        ( is-orthogonal-right-comp
          ( terminal-map Y)
          ( map-product (terminal-map A) (terminal-map B))
          ( terminal-map (unit × unit))
          ( is-orthogonal-is-equiv-right
            ( terminal-map Y)
            ( terminal-map (unit × unit))
            ( is-equiv-map-right-unit-law-product))
          ( is-orthogonal-right-product
            ( terminal-map Y)
            ( terminal-map A)
            ( terminal-map B)
            ( is-orthogonal-terminal-maps-is-null is-null-A)
            ( is-orthogonal-terminal-maps-is-null is-null-B)))
```

### Null types are closed under identity types

This remains to be formalized.

## See also

- We show that null types are closed under dependent sums in
  [`null-maps`](orthogonal-factorization-systems.null-maps.md).
- In
  [`coproducts-null-types`](orthogonal-factorization-systems.coproducts-null-types.md)
  we show that `Y`-null types are closed under
  [coproducts](foundation.coproduct-types.md) if and only if the
  [booleans](foundation.booleans.md) are `Y`-null.
