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
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.propositions
open import foundation-core.sets
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

A type is said to be {{#concept "projective" Agda=is-projective}} if there is a
choice function

$$ ((x : X) → ║P(x)║₋₁) → ║(x : X) → P(x)║₋₁$$

for every type family $P$. This condition is stronger than set-projectivity,
unless $X$ is a set.

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

### Projective types

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-projective-Level : UU (l1 ⊔ lsuc l2)
  is-projective-Level =
    (P : X → UU l2) →
    ((x : X) → is-inhabited (P x)) →
    is-inhabited ((x : X) → (P x))

  abstract
    is-prop-is-projective-Level : is-prop is-projective-Level
    is-prop-is-projective-Level =
      is-prop-Π
        ( λ P →
          is-prop-function-type
            ( is-property-is-inhabited ((x : X) → P x)))

  is-projective-prop-Level : Prop (l1 ⊔ lsuc l2)
  is-projective-prop-Level =
    ( is-projective-Level , is-prop-is-projective-Level)

is-projective : {l1 : Level} → UU l1 → UUω
is-projective X = {l2 : Level} → is-projective-Level l2 X
```

### The universe of set-projective sets

```agda
Projective-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Projective-Set l1 l2 = Σ (Set l1) (is-projective-Level l2 ∘ type-Set)

module _
  {l1 l2 : Level} (X : Projective-Set l1 l2)
  where

  set-Projective-Set : Set l1
  set-Projective-Set = pr1 X

  type-Projective-Set : UU l1
  type-Projective-Set = type-Set set-Projective-Set

  is-set-type-Projective-Set : is-set type-Projective-Set
  is-set-type-Projective-Set = is-set-type-Set set-Projective-Set

  is-projective-Projective-Set : is-projective-Level l2 type-Projective-Set
  is-projective-Projective-Set = pr2 X
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
is-projective-is-projective-lub-Level :
  {l1 : Level} (l2 l3 : Level) {X : UU l1} →
  is-projective-Level (l2 ⊔ l3) X →
  is-projective-Level l2 X
is-projective-is-projective-lub-Level l2 l3 H P h =
  map-is-inhabited
    ( λ f x → map-inv-raise (f x))
    ( H
      ( λ x → raise l3 (P x))
      ( λ x → map-is-inhabited map-raise (h x)))

is-projective-is-projective-lsuc-Level :
  {l1 : Level} (l2 : Level) {X : UU l1} →
  is-projective-Level (lsuc l2) X →
  is-projective-Level l2 X
is-projective-is-projective-lsuc-Level l2 =
  is-projective-is-projective-lub-Level l2 (lsuc l2)
```

### Set-projective sets are projective

```agda
is-projective-is-set-projective-Level :
  {l1 l2 : Level} {X : UU l1} →
  is-set X →
  is-set-projective-Level (l1 ⊔ l2) l1 X →
  is-projective-Level l2 X
is-projective-is-set-projective-Level {X = X} K H P h =
  map-is-inhabited
    ( map-inv-equiv (compute-fiber-postcomp-pr1 P id))
    ( H
      ( Σ X P)
      ( X , K)
      ( pr1 ,
        λ x → map-is-inhabited (λ y → ((x , y) , refl)) (h x))
      ( id))

is-projective-is-set-projective :
  {l1 : Level} {X : UU l1} →
  is-set X →
  is-set-projective X →
  is-projective X
is-projective-is-set-projective {l1} {X} K H {l2} =
  is-projective-is-set-projective-Level K (H {l1 ⊔ l2} {l1})
```

## See also

- The notion of set-projectivity generalizes to
  [`n`-projectivity](foundation.truncation-projective-types.md).

- The natural map `(X → A)/~ → (X → A/R)` is studied in
  [`foundation.exponents-set-quotients`](foundation.exponents-set-quotients.md)
