# The Regensburg extension of the fundamental theorem of identity types

```agda
module
  foundation.regensburg-extension-fundamental-theorem-of-identity-types
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.functoriality-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.maps-in-subuniverses
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.separated-types-subuniverses
open import foundation.structured-equality-duality
open import foundation.subuniverses
open import foundation.surjective-maps
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "Regensburg extension" Disambiguation="of the fundamental theorem of identity types" Agda=extended-fundamental-theorem-id}}
of the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
asserts that for any [subuniverse](foundation.subuniverses.md) `P`, and any
[pointed](structured-types.pointed-types.md)
[connected type](foundation.connected-types.md) `A` equipped with a type family
`B` over `A`, the following are
[logically equivalent](foundation.logical-equivalences.md):

1. Every family of maps `f : (x : A) → (* ＝ x) → B x` is a family of `P`-maps,
   i.e., a family of maps with [fibers](foundation-core.fibers-of-maps.md) in
   `P`.
2. The [total space](foundation.dependent-pair-types.md) `Σ A B` is
   [`P`-separated](foundation.separated-types-subuniverses.md), i.e., its
   [identity types](foundation-core.identity-types.md) are in `P`.

In other words, the extended fundamental theorem of
[identity types](foundation-core.identity-types.md) asserts that for any
[higher group](higher-group-theory.higher-groups.md) `BG` equipped with a
[higher group action](higher-group-theory.higher-group-actions.md) `X`, every
[homomorphism of higher group actions](higher-group-theory.homomorphisms-higher-group-actions.md)
`f : (u : BG) → (* ＝ u) → X u` consists of a family of `P` maps if and only if
the type of [orbits](higher-group-theory.orbits-higher-group-actions.md) of `X`
is `P`-separated.

**Proof:** Suppose that every family of maps `f : (x : A) → (* ＝ x) → B x` is a
family of `P`-maps. The [fiber](foundation-core.fibers-of-maps.md) of such
`f x : (* ＝ x) → B x` at `y` is [equivalent](foundation-core.equivalences.md)
to the type `(* , f * refl) ＝ (x , y)`. Our assumption is therefore equivalent
to the assumption that the type `(* , f * refl) ＝ (x , y)` is in `P` for every
`f`, `x`, and `y`. By the
[universal property of identity types](foundation.universal-property-identity-types.md),
this condition is equivalent to the condition that `(* , y') ＝ (x , y)` is in
`P` for every `y'`, `x`, and `y`. Finally, since `A` is assumed to be connected,
this condition is equivalent to the condition that `Σ A B` is `P`-separated.

This theorem was stated and proven for the first time during the
[Interactions of Proof Assistants and Mathematics](https://itp-school-2023.github.io)
summer school in Regensburg, 2023, as part of
[Egbert Rijke](https://egbertrijke.github.io)'s tutorial on formalization in
agda-unimath.

## Theorem

### The extended fundamental theorem of identity types

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  {A : UU l1} (a : A) {B : A → UU l2}
  where

  abstract
    forward-implication-extended-fundamental-theorem-id :
      is-0-connected A →
      ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)) →
      is-separated 𝒫 (Σ A B)
    forward-implication-extended-fundamental-theorem-id H K =
      forward-implication-subuniverse-equality-duality 𝒫
        ( is-in-subuniverse-equiv 𝒫)
        ( λ x f y b →
          apply-universal-property-trunc-Prop
            ( mere-eq-is-0-connected H a x)
            ( 𝒫 (fiber (f y) b))
            ( λ where refl → K f y b))

  abstract
    backward-implication-extended-fundamental-theorem-id :
      is-separated 𝒫 (Σ A B) →
      (f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)
    backward-implication-extended-fundamental-theorem-id K =
      backward-implication-subuniverse-equality-duality 𝒫
        ( is-in-subuniverse-equiv 𝒫)
        ( K)
        ( a)

  extended-fundamental-theorem-id :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-in-subuniverse-map 𝒫 (f x)) ↔
    is-separated 𝒫 (Σ A B)
  extended-fundamental-theorem-id H =
    ( forward-implication-extended-fundamental-theorem-id H ,
      backward-implication-extended-fundamental-theorem-id)
```

### The unbased extended fundamental theorem of identity types

We give a similar characterization for a binary family of types `B : A → A → 𝒰`
over a not necessarily pointed or inhabited type `A` whose elements are all
merely equal. In other words, `A` is any π₀-trivial type. The characterization
asserts that the following are equivalent:

1. For every `x : A`, every family of maps out of the identity types
   `f : (y : A) → (x ＝ y) → B x y`, is a family of `𝒫`-maps.
2. For every `x : A` the type `Σ A (B x)` is `𝒫`-separated.

This unbased extension of the fundamental theorem was not stated or proved at
the Regensburg summer school, but was later contributed by
[Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke) in January 2025.

```agda
module _
  {l1 l2 l3 : Level} (𝒫 : subuniverse (l1 ⊔ l2) l3)
  {A : UU l1} {B : A → A → UU l2}
  where

  forward-implication-extended-fundamental-theorem-unbased-id :
    ( (x y : A) → mere-eq x y) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B x y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) →
    ( (x : A) → is-separated 𝒫 (Σ A (B x)))
  forward-implication-extended-fundamental-theorem-unbased-id H K x =
    forward-implication-extended-fundamental-theorem-id 𝒫
      ( x)
      ( is-0-connected-mere-eq x (H x))
      ( K x)

  backward-implication-extended-fundamental-theorem-unbased-id :
    ( (x : A) → is-separated 𝒫 (Σ A (B x))) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B x y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y))
  backward-implication-extended-fundamental-theorem-unbased-id K x =
    backward-implication-extended-fundamental-theorem-id 𝒫 x (K x)

  extended-fundamental-theorem-unbased-id :
    ( (x y : A) → mere-eq x y) →
    ( (x : A) (f : (y : A) → (x ＝ y) → B x y)
      (y : A) → is-in-subuniverse-map 𝒫 (f y)) ↔
    ( (x : A) → is-separated 𝒫 (Σ A (B x)))
  extended-fundamental-theorem-unbased-id H =
    ( forward-implication-extended-fundamental-theorem-unbased-id H ,
      backward-implication-extended-fundamental-theorem-unbased-id)
```

## Corollaries

### Characterizing families of surjective maps out of identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} (a : A) {B : A → UU l2}
  where

  forward-implication-extended-fundamental-theorem-id-surjective :
    is-0-connected A →
    ( (f : (x : A) → (a ＝ x) → B x) → (x : A) → is-surjective (f x)) →
    is-inhabited (B a) → is-0-connected (Σ A B)
  forward-implication-extended-fundamental-theorem-id-surjective H K L =
    is-0-connected-mere-eq-is-inhabited
      ( map-trunc-Prop (fiber-inclusion B a) L)
      ( forward-implication-extended-fundamental-theorem-id
        ( is-inhabited-Prop)
        ( a)
        ( H)
        ( K))

  backward-implication-extended-fundamental-theorem-id-surjective :
    is-0-connected (Σ A B) →
    (f : (x : A) → (a ＝ x) → B x) (x : A) → is-surjective (f x)
  backward-implication-extended-fundamental-theorem-id-surjective L =
    backward-implication-extended-fundamental-theorem-id
      ( is-inhabited-Prop)
      ( a)
      ( mere-eq-is-0-connected L)

  extended-fundamental-theorem-id-surjective :
    is-0-connected A → is-inhabited (B a) →
    ( (f : (x : A) → (a ＝ x) → B x) → (x : A) → is-surjective (f x)) ↔
    is-0-connected (Σ A B)
  pr1 (extended-fundamental-theorem-id-surjective H K) L =
    forward-implication-extended-fundamental-theorem-id-surjective H L K
  pr2 ( extended-fundamental-theorem-id-surjective H K) =
    backward-implication-extended-fundamental-theorem-id-surjective
```

### Characterizing families of connected maps out of identity types

```agda
module _
  {l1 l2 : Level} (k : 𝕋)
  {A : UU l1} (a : A) {B : A → UU l2}
  where

  forward-implication-extended-fundamental-theorem-id-connected :
    is-0-connected A →
    ( (f : (x : A) → (a ＝ x) → B x) → (x : A) → is-connected-map k (f x)) →
    is-inhabited (B a) → is-connected (succ-𝕋 k) (Σ A B)
  forward-implication-extended-fundamental-theorem-id-connected H K L =
    is-connected-succ-is-connected-eq
      ( map-trunc-Prop (fiber-inclusion B a) L)
      ( forward-implication-extended-fundamental-theorem-id
        ( is-connected-Prop k)
        ( a)
        ( H)
        ( K))

  backward-implication-extended-fundamental-theorem-id-connected :
    is-connected (succ-𝕋 k) (Σ A B) →
    (f : (x : A) → (a ＝ x) → B x) (x : A) → is-connected-map k (f x)
  backward-implication-extended-fundamental-theorem-id-connected K =
    backward-implication-extended-fundamental-theorem-id
      ( is-connected-Prop k)
      ( a)
      ( λ x y → is-connected-eq-is-connected K)

  extended-fundamental-theorem-id-connected :
    is-0-connected A → is-inhabited (B a) →
    ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-connected-map k (f x)) ↔
    is-connected (succ-𝕋 k) (Σ A B)
  pr1 (extended-fundamental-theorem-id-connected H K) L =
    forward-implication-extended-fundamental-theorem-id-connected H L K
  pr2 (extended-fundamental-theorem-id-connected H K) =
    backward-implication-extended-fundamental-theorem-id-connected
```

### Characterizing families of truncated maps out of identity types

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (a : A) {B : A → UU l2}
  where

  forward-implication-extended-fundamental-theorem-id-truncated :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) → (x : A) → is-trunc-map k (f x)) →
    is-trunc (succ-𝕋 k) (Σ A B)
  forward-implication-extended-fundamental-theorem-id-truncated =
    forward-implication-extended-fundamental-theorem-id
      ( is-trunc-Prop k)
      ( a)

  backward-implication-extended-fundamental-theorem-id-truncated :
    is-trunc (succ-𝕋 k) (Σ A B) →
    (f : (x : A) → (a ＝ x) → B x) (x : A) → is-trunc-map k (f x)
  backward-implication-extended-fundamental-theorem-id-truncated =
    backward-implication-extended-fundamental-theorem-id
      ( is-trunc-Prop k)
      ( a)

  extended-fundamental-theorem-id-truncated :
    is-0-connected A →
    ((f : (x : A) → (a ＝ x) → B x) (x : A) → is-trunc-map k (f x)) ↔
    is-trunc (succ-𝕋 k) (Σ A B)
  pr1 (extended-fundamental-theorem-id-truncated H) =
    forward-implication-extended-fundamental-theorem-id-truncated H
  pr2 (extended-fundamental-theorem-id-truncated H) =
    backward-implication-extended-fundamental-theorem-id-truncated
```

## See also

The Regensburg extension of the fundamental theorem is used in the following
files:

- In
  [`higher-group-theory.free-higher-group-actions`](higher-group-theory.free-higher-group-actions.md)
  it is used to show that a higher group action is free if and only its total
  space is a set.
- In
  [`higher-group-theory.transitive-higher-group-actions`](higher-group-theory.transitive-higher-group-actions.md)
  it is used to show that a higher group action is transitive if and only if its
  total space is connected.

## References

Two special cases of the extended fundamental theorem of identity types are
stated in {{#cite Rij22}}: The case where `P` is the subuniverse of
`k`-truncated types is stated as Theorem 19.6.2; and the case where `P` is the
subuniverse of inhabited types is stated as Exercise 19.14.

{{#bibliography}}
