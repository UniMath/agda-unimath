# The poset of premetric structures on a type

```agda
module metric-spaces.ordering-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric structure](metric-spaces.premetric-structures.md) `U` on a type `A`
is {{#concept "finer" Disambiguation="premetric on a type" Agda=leq-Premetric}}
than another premetric `V` if `(U d)`-neighborhoods are `(V d)`-neighborhoods
for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `d`.
This gives a [partial order](order-theory.posets.md) on premetric structures on
`A`.

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V : Premetric l2 A)
  where

  leq-prop-Premetric : Prop (l1 ⊔ l2)
  leq-prop-Premetric =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → hom-Prop (U d x y) (V d x y))))

  leq-Premetric : UU (l1 ⊔ l2)
  leq-Premetric = type-Prop leq-prop-Premetric

  is-prop-leq-Premetric : is-prop leq-Premetric
  is-prop-leq-Premetric = is-prop-type-Prop leq-prop-Premetric
```

## Properties

### The ordering on premetric structures is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U : Premetric l2 A)
  where

  refl-leq-Premetric : leq-Premetric U U
  refl-leq-Premetric d x y H = H

  leq-eq-Premetric : (V : Premetric l2 A) → (U ＝ V) → leq-Premetric U V
  leq-eq-Premetric .U refl = refl-leq-Premetric
```

### The ordering on premetric structures is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V W : Premetric l2 A)
  where

  transitive-leq-Premetric :
    leq-Premetric V W → leq-Premetric U V → leq-Premetric U W
  transitive-leq-Premetric H K d x y = H d x y ∘ K d x y
```

### The ordering on premetric structures is antisymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (U V : Premetric l2 A)
  where

  antisymmetric-leq-Premetric :
    leq-Premetric U V → leq-Premetric V U → U ＝ V
  antisymmetric-leq-Premetric I J =
    eq-Eq-Premetric
      ( U)
      ( V)
      ( λ d x y → (I d x y , J d x y))
```
