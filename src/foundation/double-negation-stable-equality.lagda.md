# Double negation stable equality

```agda
module foundation.double-negation-stable-equality where

open import foundation-core.double-negation-stable-equality public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import logic.double-negation-dense-subtypes
```

</details>

## Idea

A type `A` is said to have
{{#concept "double negation stable equality" Disambiguation="type" Agda=has-double-negation-stable-equality}}
if `x ＝ y` has
[double negation elimination](logic.double-negation-elimination.md) for every
`x y : A`. By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
types with double negation stable equality are [sets](foundation-core.sets.md).

## Properties

## Homotopies of maps on double negation dense subsets of a type with double negation stable equality

Given a double negation dense subtype `P ⊆ X` and two functions `f` and
`g : X → Y` into a type `Y` with double negation stable equality. Then if `f`
and `g` are homotopic on `P`, they are homotopic on all of `X`.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (P : double-negation-dense-subtype l3 X)
  (H : has-double-negation-stable-equality Y)
  where

  htpy-htpy-on-double-negation-dense-subtype :
    (f g : X → Y)
    (K :
      (x : type-double-negation-dense-subtype P) →
      f (inclusion-double-negation-dense-subtype P x) ＝
      g (inclusion-double-negation-dense-subtype P x)) →
    (x : X) → f x ＝ g x
  htpy-htpy-on-double-negation-dense-subtype f g K x =
    H ( f x)
      ( g x)
      ( map-double-negation
        ( K ∘ pair x)
        ( is-double-negation-dense-double-negation-dense-subtype P x))
```

As a corollary, if `f` is constant on `P`, it is constant of all of `X`. This is
Lemma 3.4 in {{#cite Esc13}}

```agda
  htpy-const-htpy-const-on-double-negation-dense-subtype :
    (f : X → Y) (y : Y)
    (K :
      (x : type-double-negation-dense-subtype P) →
      f (inclusion-double-negation-dense-subtype P x) ＝ y) →
    (x : X) → f x ＝ y
  htpy-const-htpy-const-on-double-negation-dense-subtype f y =
    htpy-htpy-on-double-negation-dense-subtype f (λ _ → y)
```

## See also

- Every type with a
  [tight apartness relation](foundation.tight-apartness-relations.md) has double
  negation stable equality. Conversely, every type with double negation stable
  equality has a tight, symmetric, antireflexive relation. However, this
  relation need not be cotransitive.

## References

{{#bibliography}}

## External links

- [double negation stable equality](https://ncatlab.org/nlab/show/decidable+equality)
  at $n$Lab
