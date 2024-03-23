# The type theoretic replacement axiom

```agda
module foundation.replacement where
```

<details><summary>Imports</summary>

```agda
open import foundation.images
open import foundation.locally-small-types
open import foundation.universe-levels

open import foundation-core.small-types
```

</details>

## Idea

The **type theoretic replacement axiom** asserts that the
[image](foundation.images.md) of a map `f : A → B` from a
[small type](foundation-core.small-types.md) `A` into a
[locally small type](foundation.locally-small-types.md) `B` is small.

## Statement

```agda
instance-replacement :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) →
  UU (lsuc l ⊔ l1 ⊔ l2)
instance-replacement l {A = A} {B} f =
  is-small l A → is-locally-small l B → is-small l (im f)

replacement-axiom-Level : (l l1 l2 : Level) → UU (lsuc l ⊔ lsuc l1 ⊔ lsuc l2)
replacement-axiom-Level l l1 l2 =
  {A : UU l1} {B : UU l2} (f : A → B) → instance-replacement l f

replacement-axiom : UUω
replacement-axiom = {l l1 l2 : Level} → replacement-axiom-Level l l1 l2
```

## Postulate

```agda
postulate
  replacement : replacement-axiom
```

```agda
replacement' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-locally-small l1 B → is-small l1 (im f)
replacement' f = replacement f is-small'
```

## References

- Theorem 4.6 in {{#cite Rij17}}.
- Section 2.19 in {{#cite SymmetryBook}}.

{{#bibliography}}
