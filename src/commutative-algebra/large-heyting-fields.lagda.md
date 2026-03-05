# Large Heyting fields

```agda
module commutative-algebra.large-heyting-fields where
```

<details><summary>Imports</summary>

```agda
open import group-theory.invertible-elements-large-monoids
open import commutative-algebra.large-commutative-rings
open import foundation.negation
open import group-theory.large-monoids
open import foundation.negated-equality
open import foundation.disjunction
open import foundation.propositions
open import group-theory.large-commutative-monoids
open import foundation.universe-levels

```

</details>

## Idea

## Definition

```agda
record
  Large-Heyting-Field
  (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Heyting-Field

  field
    large-commutative-ring-Large-Heyting-Field : Large-Commutative-Ring α β

  type-Large-Heyting-Field : (l : Level) → UU (α l)
  type-Large-Heyting-Field =
    type-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  large-commutative-monoid-mul-Large-Heyting-Field :
    Large-Commutative-Monoid α β
  large-commutative-monoid-mul-Large-Heyting-Field =
    multiplicative-large-commutative-monoid-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  large-monoid-mul-Large-Heyting-Field : Large-Monoid α β
  large-monoid-mul-Large-Heyting-Field =
    large-monoid-Large-Commutative-Monoid
      large-commutative-monoid-mul-Large-Heyting-Field

  is-invertible-element-prop-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field l) → Prop (α l ⊔ β l lzero)
  is-invertible-element-prop-Large-Heyting-Field =
    is-invertible-element-prop-Large-Monoid large-monoid-mul-Large-Heyting-Field

  is-invertible-element-Large-Heyting-Field :
    {l : Level} (x : type-Large-Heyting-Field l) → UU (α l ⊔ β l lzero)
  is-invertible-element-Large-Heyting-Field x =
    type-Prop (is-invertible-element-prop-Large-Heyting-Field x)

  add-Large-Heyting-Field :
    {l1 l2 : Level} →
    type-Large-Heyting-Field l1 → type-Large-Heyting-Field l2 →
    type-Large-Heyting-Field (l1 ⊔ l2)
  add-Large-Heyting-Field =
    add-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  zero-Large-Heyting-Field : type-Large-Heyting-Field lzero
  zero-Large-Heyting-Field =
    zero-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  is-zero-prop-Large-Heyting-Field :
    {l : Level} → type-Large-Heyting-Field l → Prop (β l lzero)
  is-zero-prop-Large-Heyting-Field =
    is-zero-prop-Large-Commutative-Ring
      ( large-commutative-ring-Large-Heyting-Field)

  is-zero-Large-Heyting-Field :
    {l : Level} → type-Large-Heyting-Field l → UU (β l lzero)
  is-zero-Large-Heyting-Field x =
    type-Prop (is-zero-prop-Large-Heyting-Field x)

  one-Large-Heyting-Field : type-Large-Heyting-Field lzero
  one-Large-Heyting-Field =
    one-Large-Commutative-Ring large-commutative-ring-Large-Heyting-Field

  field
    is-local-Large-Heyting-Field :
      {l1 l2 : Level}
      (x : type-Large-Heyting-Field l1) (y : type-Large-Heyting-Field l2) →
      is-invertible-element-Large-Heyting-Field (add-Large-Heyting-Field x y) →
      disjunction-type
        ( is-invertible-element-Large-Heyting-Field x)
        ( is-invertible-element-Large-Heyting-Field y)

    is-nontrivial-Large-Heyting-Field :
      zero-Large-Heyting-Field ≠ one-Large-Heyting-Field

    is-zero-is-not-invertible-element-Large-Heyting-Field :
      {l : Level} (x : type-Large-Heyting-Field l) →
      ¬ is-invertible-element-Large-Heyting-Field x →
      is-zero-Large-Heyting-Field x
```
