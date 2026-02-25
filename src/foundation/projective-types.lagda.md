# Projective types

```agda
module foundation.projective-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.surjective-maps
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-types
```

</details>

## Idea

A type `X` is said to be {{#concept "set-projective" Agda=is-set-projective}} if
for every [surjective map](foundation.surjective-maps.md) `f : A ↠ B` onto a
[set](foundation-core.sets.md) `B` the
[postcomposition function](foundation-core.postcomposition-functions.md)

```text
  (X → A) → (X → B)
```

is surjective. This is [equivalent](foundation.logical-equivalences.md) to the
condition that for every
[equivalence relation](foundation-core.equivalence-relations.md) `R` on a type
`A` the natural map

```text
  (X → A)/~ → (X → A/R)
```

is an [equivalence](foundation-core.equivalences.md). The latter map is always
an [embedding](foundation-core.embeddings.md), and it is an equivalence for
every `X`, `A`, and `R` if and only if
[the axiom of choice](foundation.axiom-of-choice.md) holds.

The notion of set-projectiveness generalizes to
{{#concept "`n`-projectiveness" Agda=is-trunc-projective}}, for every
[natural number](elementary-number-theory.natural-numbers.md) `n`. A type `X` is
said to be `k`-projective if the postcomposition function `(X → A) → (X → B)` is
surjective for every `k-1`-[connected map](foundation.connected-maps.md)
`f : A → B` into a `k`-[truncated type](foundation-core.truncated-types.md) `B`.

## Definitions

### Set-projective types

```agda
is-set-projective-Level :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-set-projective-Level l2 l3 X =
  (A : UU l2) (B : Set l3) (f : A ↠ type-Set B) →
  is-surjective (postcomp X (map-surjection f))

is-set-projective : {l1 : Level} → UU l1 → UUω
is-set-projective X = {l2 l3 : Level} → is-set-projective-Level l2 l3 X
```

### `k`-projective types

```agda
is-trunc-projective-Level :
  {l1 : Level} (l2 l3 : Level) → ℕ → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-trunc-projective-Level l2 l3 k X =
  ( A : UU l2) (B : Truncated-Type l3 (truncation-level-ℕ k))
  ( f :
    connected-map
      ( truncation-level-minus-one-ℕ k)
      ( A)
      ( type-Truncated-Type B)) →
  is-surjective (postcomp X (map-connected-map f))

is-trunc-projective : {l1 : Level} → ℕ → UU l1 → UUω
is-trunc-projective k X = {l2 l3 : Level} → is-trunc-projective-Level l2 l3 k X
```

### Alternative statement of set-projectivity

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-projective-Level' : UU (l1 ⊔ lsuc l2)
  is-projective-Level' =
    (P : X → UU l2) →
    ((x : X) → is-inhabited (P x)) →
    is-inhabited ((x : X) → (P x))

  abstract
    is-prop-is-projective-Level' : is-prop is-projective-Level'
    is-prop-is-projective-Level' =
      is-prop-Π
        ( λ P →
          is-prop-function-type
            ( is-property-is-inhabited ((x : X) → P x)))

  is-projective-prop-Level' : Prop (l1 ⊔ lsuc l2)
  is-projective-prop-Level' =
    ( is-projective-Level' , is-prop-is-projective-Level')

is-projective' : {l1 : Level} → UU l1 → UUω
is-projective' X = {l2 : Level} → is-projective-Level' l2 X
```

## See also

- The natural map `(X → A)/~ → (X → A/R)` is studied in
  [`foundation.exponents-set-quotients`](foundation.exponents-set-quotients.md)
