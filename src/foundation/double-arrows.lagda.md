# Double arrows

```agda
module foundation.double-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "double arrow" Disambiguation="between types" Agda=double-arrow}}
is a [pair](foundation.dependent-pair-types.md) of types `A`, `B`
[equipped](foundation.structure.md) with a pair of
[maps](foundation.function-types.md) `f, g : A → B`.

We draw a double arrow as

```text
     A
    | |
  f | | g
    | |
    ∨ ∨
     B
```

where `f` is the first map in the structure and `g` is the second map in the
structure. We also call `f` the _left map_ and `g` the _right map_. By
convention, [homotopies](foundation-core.homotopies.md) go from left to right.

## Definitions

### Double arrows

```agda
double-arrow : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
double-arrow l1 l2 = Σ (UU l1) (λ A → Σ (UU l2) (λ B → (A → B) × (A → B)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (g : A → B)
  where

  make-double-arrow : double-arrow l1 l2
  pr1 make-double-arrow = A
  pr1 (pr2 make-double-arrow) = B
  pr1 (pr2 (pr2 make-double-arrow)) = f
  pr2 (pr2 (pr2 make-double-arrow)) = g
```

### Components of a double arrow

```agda
module _
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  domain-double-arrow : UU l1
  domain-double-arrow = pr1 a

  codomain-double-arrow : UU l2
  codomain-double-arrow = pr1 (pr2 a)

  left-map-double-arrow : domain-double-arrow → codomain-double-arrow
  left-map-double-arrow = pr1 (pr2 (pr2 a))

  right-map-double-arrow : domain-double-arrow → codomain-double-arrow
  right-map-double-arrow = pr2 (pr2 (pr2 a))
```

## See also

- Colimits of double arrows are
  [coequalizers](synthetic-homotopy-theory.coequalizers.md)
