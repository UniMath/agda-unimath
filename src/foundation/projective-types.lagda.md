# Projective types

```agda
module foundation.projective-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.iterated-successors-truncation-levels
open import foundation.postcomposition-functions
open import foundation.raising-universe-levels
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.equivalences
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

### 𝑘-projective types

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

We also give the alternative definition of set-projectivity as having a choice
function

$$ ((x : X) → ║P(x)║₋₁) → ║(x : X) → P(x)║₋₁$$

for every type family $P$.

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

### The universe of set-projective sets

```agda
Projective-Set' : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Projective-Set' l1 l2 = Σ (Set l1) (is-projective-Level' l2 ∘ type-Set)

module _
  {l1 l2 : Level} (X : Projective-Set' l1 l2)
  where

  set-Projective-Set' : Set l1
  set-Projective-Set' = pr1 X

  type-Projective-Set' : UU l1
  type-Projective-Set' = type-Set set-Projective-Set'

  is-set-type-Projective-Set' : is-set type-Projective-Set'
  is-set-type-Projective-Set' = is-set-type-Set set-Projective-Set'

  is-projective-Projective-Set' : is-projective-Level' l2 type-Projective-Set'
  is-projective-Projective-Set' = pr2 X
```

## Properties

### Lowering universe levels for projectivity

```agda
is-projective-is-projective-lub-Level' :
  {l1 : Level} (l2 l3 : Level) {X : UU l1} →
  is-projective-Level' (l2 ⊔ l3) X →
  is-projective-Level' l2 X
is-projective-is-projective-lub-Level' l2 l3 H P h =
  map-is-inhabited
    ( λ f x → map-inv-raise (f x))
    ( H
      ( λ x → raise l3 (P x))
      ( λ x → map-is-inhabited map-raise (h x)))

is-projective-is-projective-lsuc-Level' :
  {l1 : Level} (l2 : Level) {X : UU l1} →
  is-projective-Level' (lsuc l2) X →
  is-projective-Level' l2 X
is-projective-is-projective-lsuc-Level' l2 =
  is-projective-is-projective-lub-Level' l2 (lsuc l2)
```

### Set-projectivity is equivalent to 0-projectivity

```agda
is-set-projective-is-0-projective-Level :
  {l1 l2 l3 : Level} {X : UU l1} →
  is-trunc-projective-Level l2 l3 zero-ℕ X →
  is-set-projective-Level l2 l3 X
is-set-projective-is-0-projective-Level H A B f =
  H ( A)
    ( type-Set B , is-set-type-Set B)
    ( map-surjection f ,
      is-neg-one-connected-map-is-surjective (is-surjective-map-surjection f))

is-0-projective-is-set-projective-Level :
  {l1 l2 l3 : Level} {X : UU l1} →
  is-set-projective-Level l2 l3 X →
  is-trunc-projective-Level l2 l3 zero-ℕ X
is-0-projective-is-set-projective-Level H A B f =
  H ( A)
    ( type-Truncated-Type B , is-trunc-type-Truncated-Type B)
    ( neg-one-connected-map-surjective-map f)

is-set-projective-is-0-projective :
  {l1 : Level} {X : UU l1} →
  is-trunc-projective zero-ℕ X →
  is-set-projective X
is-set-projective-is-0-projective H {l2} {l3} =
  is-set-projective-is-0-projective-Level (H {l2} {l3})

is-trunc-projective-zero-ℕ-is-set-projective :
  {l1 : Level} {X : UU l1} →
  is-set-projective X →
  is-trunc-projective zero-ℕ X
is-trunc-projective-zero-ℕ-is-set-projective H {l2} {l3} =
  is-0-projective-is-set-projective-Level (H {l2} {l3})
```

### 𝑘-projective 𝑘-types are (𝑘 + 𝑛)-projective for all 𝑛

```agda
is-add-trunc-projective-is-trunc-projective :
  {l1 : Level} (k n : ℕ) {X : UU l1} →
  is-trunc (truncation-level-ℕ k) X →
  is-trunc-projective k X →
  is-trunc-projective (k +ℕ n) X
is-add-trunc-projective-is-trunc-projective {l1} k n {X} K H A B f h =
  map-is-inhabited
    ( map-equiv (compute-Π-fiber-postcomp X (map-connected-map f) h))
    ( map-is-inhabited
      ( map-inv-equiv
        ( compute-fiber-postcomp-pr1 (fiber (map-connected-map f) ∘ h) id))
      ( H ( Σ X (fiber (map-connected-map f) ∘ h))
          ( X , K)
          ( pr1 ,
            λ x →
            is-connected-equiv'
              ( inv-equiv-fiber-pr1
                ( fiber (map-connected-map f) ∘ h)
                ( x))
              ( is-connected-is-connected-add+2-𝕋
                ( truncation-level-minus-one-ℕ k)
                ( truncation-level-minus-two-ℕ n)
                ( tr
                  ( λ t →
                    is-connected t (fiber (map-connected-map f) (h x)))
                  ( add+2-truncation-level-minus-one-ℕ k n)
                  ( is-connected-map-connected-map f (h x)))))
          ( id)))
```

### Projective types in the alternative sense are 𝑛-projective for all 𝑛

```agda
is-trunc-projective-is-projective-Level' :
  {l1 : Level} (l2 l3 : Level) (n : ℕ) {X : UU l1} →
  is-projective-Level'(l2 ⊔ l3) X →
  is-trunc-projective-Level l2 l3 n X
is-trunc-projective-is-projective-Level' l2 l3 n {X} H A B f h =
  map-is-inhabited
    ( map-equiv (compute-Π-fiber-postcomp X (map-connected-map f) h))
    ( H ( λ x → fiber (map-connected-map f) (h x))
        ( λ x →
          is-inhabited-is-connected (is-connected-map-connected-map f (h x))))

is-trunc-projective-is-projective' :
  {l1 : Level} (n : ℕ) {X : UU l1} →
  is-projective' X →
  is-trunc-projective n X
is-trunc-projective-is-projective' n H {l2} {l3} =
  is-trunc-projective-is-projective-Level' l2 l3 n (H {l2 ⊔ l3})
```

## See also

- The natural map `(X → A)/~ → (X → A/R)` is studied in
  [`foundation.exponents-set-quotients`](foundation.exponents-set-quotients.md)
