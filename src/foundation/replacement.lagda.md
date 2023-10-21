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
  {A : UU l1} {B : UU l2} → (f : A → B) → instance-replacement l f

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

- Egbert Rijke, Theorem 4.6 in _The join construction_, 2017
  ([arXiv:1701.07538](https://arxiv.org/abs/1701.07538),
  [DOI:10.48550](https://doi.org/10.48550/arXiv.1701.07538))
- Marc Bezem, Ulrik Buchholtz, Pierre Cagne, Bjørn Ian Dundas, and Daniel R.
  Grayson, Section 2.19 of _Symmetry_
  ([newest version](https://unimath.github.io/SymmetryBook/book.pdf),
  [GitHub](https://github.com/UniMath/SymmetryBook))
