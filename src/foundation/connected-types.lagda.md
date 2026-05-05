# Connected types

```agda
module foundation.connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.diagonal-maps-of-types
open import foundation.equivalences-contractible-types
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.retracts-of-types
open import foundation-core.subuniverse-of-contractible-types
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be
{{#concept "`k`-connected" Disambiguation="type" Agda=is-connected Agda=Connected-Type}}
if its `k`-[truncation](foundation.truncations.md) is
[contractible](foundation-core.contractible-types.md).

## Definition

### The predicate of being a `k`-connected type

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  is-connected-Prop : Prop l
  is-connected-Prop = is-contr-Prop (type-trunc k A)

  is-connected : UU l
  is-connected = type-Prop is-connected-Prop

  is-prop-is-connected : is-prop is-connected
  is-prop-is-connected = is-prop-type-Prop is-connected-Prop
```

### The type of `k`-connected types

```agda
Connected-Type : (l : Level) (k : 𝕋) → UU (lsuc l)
Connected-Type l k = Σ (UU l) (is-connected k)

module _
  {l : Level} {k : 𝕋} (A : Connected-Type l k)
  where

  type-Connected-Type : UU l
  type-Connected-Type = pr1 A

  is-connected-Connected-Type : is-connected k type-Connected-Type
  is-connected-Connected-Type = pr2 A
```

## Properties

### All types are `(-2)`-connected

```agda
is-neg-two-connected : {l : Level} (A : UU l) → is-connected neg-two-𝕋 A
is-neg-two-connected A = is-trunc-type-trunc
```

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-exponential-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (diagonal-exponential (type-Truncated-Type B) A)
is-equiv-diagonal-exponential-is-connected {k = k} {A} B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( diagonal-exponential (type-Truncated-Type B) (type-trunc k A))
    ( is-equiv-diagonal-exponential-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)

is-connected-is-equiv-diagonal-exponential :
  {l1 : Level} {k : 𝕋} {A : UU l1} →
  ( {l2 : Level} (B : Truncated-Type l2 k) →
    is-equiv (diagonal-exponential (type-Truncated-Type B) A)) →
  is-connected k A
is-connected-is-equiv-diagonal-exponential {k = k} {A} H =
  tot
    ( λ x →
      function-dependent-universal-property-trunc
        ( Id-Truncated-Type' (trunc k A) x))
    ( tot
      ( λ _ → htpy-eq)
      ( center (is-contr-map-is-equiv (H (trunc k A)) unit-trunc)))
```

### Being connected is invariant under equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-equiv :
    (f : A → B) → is-equiv f → is-connected k B → is-connected k A
  is-connected-is-equiv f e =
    is-contr-is-equiv
      ( type-trunc k B)
      ( map-trunc k f)
      ( is-equiv-map-equiv-trunc k (f , e))

  is-connected-equiv :
    A ≃ B → is-connected k B → is-connected k A
  is-connected-equiv f =
    is-connected-is-equiv (map-equiv f) (is-equiv-map-equiv f)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-equiv' :
    A ≃ B → is-connected k A → is-connected k B
  is-connected-equiv' f = is-connected-equiv (inv-equiv f)

  is-connected-is-equiv' :
    (f : A → B) → is-equiv f → is-connected k A → is-connected k B
  is-connected-is-equiv' f e = is-connected-equiv' (f , e)
```

### Retracts of `k`-connected types are `k`-connected

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-retract-of :
    A retract-of B → is-connected k B → is-connected k A
  is-connected-retract-of R =
    is-contr-retract-of (type-trunc k B) (retract-of-trunc-retract-of R)
```

### A contractible type is `k`-connected for any `k`

```agda
module _
  {l1 : Level} (k : 𝕋) {A : UU l1}
  where

  is-connected-is-contr : is-contr A → is-connected k A
  is-connected-is-contr H =
    is-connected-is-equiv-diagonal-exponential
      ( λ B → is-equiv-diagonal-exponential-is-contr H (type-Truncated-Type B))
```

### A type that is `k`-connected and `k`-truncated is contractible

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  is-contr-is-connected-is-trunc : is-trunc k A → is-connected k A → is-contr A
  is-contr-is-connected-is-trunc H =
    is-contr-equiv (type-trunc k A) (equiv-unit-trunc (A , H))
```

### A type that is `(k+1)`-connected is `k`-connected

```agda
is-connected-is-connected-succ-𝕋 :
  {l1 : Level} (k : 𝕋) {A : UU l1} →
  is-connected (succ-𝕋 k) A → is-connected k A
is-connected-is-connected-succ-𝕋 k H =
  is-connected-is-equiv-diagonal-exponential
    ( λ B →
      is-equiv-diagonal-exponential-is-connected
        ( truncated-type-succ-Truncated-Type k B)
        ( H))
```

### An inhabited type `A` is `k + 1`-connected if and only if its identity types are `k`-connected

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  abstract
    is-inhabited-is-connected :
      is-connected (succ-𝕋 k) A → is-inhabited A
    is-inhabited-is-connected H =
      map-universal-property-trunc
        ( truncated-type-Prop k (is-inhabited-Prop A))
        ( unit-trunc-Prop)
        ( center H)

  abstract
    is-connected-eq-is-connected :
      is-connected (succ-𝕋 k) A → {x y : A} → is-connected k (x ＝ y)
    is-connected-eq-is-connected H {x} {y} =
      is-contr-equiv
        ( unit-trunc x ＝ unit-trunc y)
        ( effectiveness-trunc k x y)
        ( is-prop-is-contr H (unit-trunc x) (unit-trunc y))

  abstract
    is-connected-succ-is-connected-eq :
      is-inhabited A → ((x y : A) → is-connected k (x ＝ y)) →
      is-connected (succ-𝕋 k) A
    is-connected-succ-is-connected-eq H K =
      apply-universal-property-trunc-Prop H
        ( is-connected-Prop (succ-𝕋 k) A)
        ( λ a →
          ( unit-trunc a) ,
          ( function-dependent-universal-property-trunc
            ( Id-Truncated-Type
              ( truncated-type-succ-Truncated-Type
                ( succ-𝕋 k)
                ( trunc (succ-𝕋 k) A))
              ( unit-trunc a))
            ( λ x →
              map-universal-property-trunc
                ( Id-Truncated-Type
                  ( trunc (succ-𝕋 k) A)
                  ( unit-trunc a)
                  ( unit-trunc x))
                ( λ where refl → refl)
                ( center (K a x)))))
```

### The total space of a family of `k`-connected types over a `k`-connected type is `k`-connected

```agda
is-connected-Σ :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  is-connected k A → ((x : A) → is-connected k (B x)) →
  is-connected k (Σ A B)
is-connected-Σ k H K =
  is-contr-equiv _ (equiv-trunc k (equiv-pr1 K) ∘e equiv-trunc-Σ k) H
```

### If the total space of a family of `k`-connected types is `k`-connected so is the base

**Proof.** We compute

```text
  ║Σ (x : A), B x║ₖ ≃ ║Σ (x : A), ║B x║ₖ║ₖ by equiv-trunc-Σ
                    ≃ ║Σ (x : A), 1 ║ₖ      by k-connectedness of B
                    ≃ ║A║ₖ                  by the right unit law of Σ
```

and so, in particular, if the total space is `k`-connected then so is the base.
∎

```agda
is-connected-base :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  ((x : A) → is-connected k (B x)) → is-connected k (Σ A B) → is-connected k A
is-connected-base k {A} {B} K =
  is-contr-equiv'
    ( type-trunc k (Σ A B))
    ( equivalence-reasoning
      type-trunc k (Σ A B)
      ≃ type-trunc k (Σ A (type-trunc k ∘ B)) by equiv-trunc-Σ k
      ≃ type-trunc k A by equiv-trunc k (right-unit-law-Σ-is-contr K))
```

### If the domain of `f` is `k+1`-connected, then the `k+1`-truncation of `f` is `k`-truncated

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-trunc-map-trunc-succ-is-succ-connected-domain :
    is-connected (succ-𝕋 k) A → is-trunc-map k (map-trunc (succ-𝕋 k) f)
  is-trunc-map-trunc-succ-is-succ-connected-domain c =
    is-trunc-map-is-trunc-succ-codomain-is-contr-domain c is-trunc-type-trunc
```
