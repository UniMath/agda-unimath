# Universal property of contractible types

```agda
open import foundation.function-extensionality-axiom

module foundation.universal-property-contractible-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.singleton-induction
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

The
{{#concept "dependent universal property of [contractible types](foundation-core.contractible-types.md)" Agda=dependent-universal-property-contr}}
states that, given a point `a : A`, the evaluating map

```text
  ev-point a P : ((x : A) → P x) → P a
```

is an [equivalence](foundation-core.equivalences.md) for every type family
`P : A → 𝒰`.

The condition that `ev-point` has a [section](foundation-core.sections.md)

```text
  P a → ((x : A) → P x)
```

is another way of phrasing that the type satisfies
[singleton induction](foundation.singleton-induction.md). Furthermore, the
condition that `ev-point` has a [retraction](foundation-core.retractions.md)
asserts that all dependent functions `(x : A) → P x` are fully determined by
their value at `a`, thus, in particular, that the section of `ev-point` is
unique.

## Definitions

### The dependent universal property of contractible types

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  dependent-universal-property-contr : UUω
  dependent-universal-property-contr =
    {l : Level} (P : A → UU l) → is-equiv (ev-point a {P})
```

### The universal property of contractible types

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  universal-property-contr : UUω
  universal-property-contr = {l : Level} (X : UU l) → is-equiv (ev-point' a {X})
```

## Properties

### The universal property of contractible types follows from the dependent universal property

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  universal-property-dependent-universal-property-contr :
    dependent-universal-property-contr a → universal-property-contr a
  universal-property-dependent-universal-property-contr dup-contr {l} X =
    dup-contr (λ _ → X)
```

### Types satisfying the universal property of contractible types are contractible

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-contr-is-equiv-ev-point :
      is-equiv (ev-point' a {A}) → is-contr A
    pr1 (is-contr-is-equiv-ev-point H) = a
    pr2 (is-contr-is-equiv-ev-point H) =
      htpy-eq
        ( ap
          ( pr1)
          ( eq-is-contr'
            ( is-contr-map-is-equiv H a)
            ( (λ _ → a) , refl)
            ( id , refl)))

  abstract
    is-contr-universal-property-contr :
      universal-property-contr a → is-contr A
    is-contr-universal-property-contr up-contr =
      is-contr-is-equiv-ev-point (up-contr A)
```

### Types satisfying the dependent universal property of contractible types are contractible

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    is-contr-dependent-universal-property-contr :
      dependent-universal-property-contr a → is-contr A
    is-contr-dependent-universal-property-contr dup-contr =
      is-contr-universal-property-contr a
        ( universal-property-dependent-universal-property-contr a dup-contr)
```

### Types that are contractible satisfy the dependent universal property

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    dependent-universal-property-contr-is-contr :
      is-contr A → dependent-universal-property-contr a
    dependent-universal-property-contr-is-contr H P =
      is-equiv-is-invertible
        ( ind-singleton a H P)
        ( compute-ind-singleton a H P)
        ( λ f →
          eq-htpy
            ( ind-singleton a H
              ( λ x → ind-singleton a H P (f a) x ＝ f x)
              ( compute-ind-singleton a H P (f a))))

  equiv-dependent-universal-property-contr :
    is-contr A → {l : Level} (B : A → UU l) → ((x : A) → B x) ≃ B a
  pr1 (equiv-dependent-universal-property-contr H P) = ev-point a
  pr2 (equiv-dependent-universal-property-contr H P) =
    dependent-universal-property-contr-is-contr H P

  apply-dependent-universal-property-contr :
    is-contr A → {l : Level} (B : A → UU l) → (B a → ((x : A) → B x))
  apply-dependent-universal-property-contr H P =
    map-inv-equiv (equiv-dependent-universal-property-contr H P)
```

### Types that are contractible satisfy the universal property

```agda
module _
  {l1 : Level} {A : UU l1} (a : A)
  where

  abstract
    universal-property-contr-is-contr :
      is-contr A → universal-property-contr a
    universal-property-contr-is-contr H =
      universal-property-dependent-universal-property-contr a
        ( dependent-universal-property-contr-is-contr a H)

  equiv-universal-property-contr :
    is-contr A → {l : Level} (X : UU l) → (A → X) ≃ X
  pr1 (equiv-universal-property-contr H X) = ev-point' a
  pr2 (equiv-universal-property-contr H X) =
    universal-property-contr-is-contr H X

  apply-universal-property-contr :
    is-contr A → {l : Level} (X : UU l) → X → (A → X)
  apply-universal-property-contr H X =
    map-inv-equiv (equiv-universal-property-contr H X)
```

## See also

- [Singleton induction](foundation.singleton-induction.md)
- [Universal property of contractible types with respect to pointed types and maps](structured-types.pointed-universal-property-contractible-types.md)
