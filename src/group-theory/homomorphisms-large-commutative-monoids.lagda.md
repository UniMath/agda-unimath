# Homomorphisms of large commutative monoids

```agda
module group-theory.homomorphisms-large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.homomorphisms-commutative-monoids
open import group-theory.homomorphisms-large-monoids
open import group-theory.large-commutative-monoids
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of large commutative monoids" Agda=hom-Large-Commutative-Monoid}}
from a [large commutative monoid](group-theory.large-commutative-monoids.md) `M`
to a large monoid `N` is a
[homomorphism](group-theory.homomorphisms-large-semigroups.md) of their
underlying [large semigroups](group-theory.large-semigroups.md) that preserves
the unit.

## Definition

We create a single-field record to ensure that the source and target large
commutative monoids can be determined implicitly from the homomorphism.

```agda
record
  hom-Large-Commutative-Monoid
    {α β : Level → Level}
    {γ δ : Level → Level → Level}
    (M : Large-Commutative-Monoid α γ)
    (N : Large-Commutative-Monoid β δ) :
    UUω
  where

  constructor
    make-hom-Large-Commutative-Monoid

  field
    hom-large-monoid-hom-Large-Commutative-Monoid :
      hom-Large-Monoid
        ( large-monoid-Large-Commutative-Monoid M)
        ( large-monoid-Large-Commutative-Monoid N)

open hom-Large-Commutative-Monoid public
```

## Properties

### Small commutative monoid homomorphisms from large ones

```agda
module _
  {α β : Level → Level}
  {γ δ : Level → Level → Level}
  {M : Large-Commutative-Monoid α γ}
  {N : Large-Commutative-Monoid β δ}
  (f : hom-Large-Commutative-Monoid M N)
  where

  hom-commutative-monoid-hom-Large-Commutative-Monoid :
    (l : Level) →
    hom-Commutative-Monoid
      ( commutative-monoid-Large-Commutative-Monoid M l)
      ( commutative-monoid-Large-Commutative-Monoid N l)
  hom-commutative-monoid-hom-Large-Commutative-Monoid =
    hom-monoid-hom-Large-Monoid
      ( hom-large-monoid-hom-Large-Commutative-Monoid f)
```
