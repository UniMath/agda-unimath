# Double lifts of families of elements

```agda
module orthogonal-factorization-systems.double-lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import orthogonal-factorization-systems.lifts-families-of-elements
```

</details>

## Idea

Consider a family of elements `b : (i : I) → B i (a i)` over a family of
elements `a : (i : I) → A i` and consider a family of types

```text
  C : (i : I) (x : A i) → B i x → 𝒰.
```

Recall that `b` is also a
[dependent lift](orthogonal-factorization-systems.lifts-families-of-elements.md)
of the family of elements `a`. The type of
{{#concept "dependent double lifts" Disambiguation="family of elements" Agda=dependent-double-lift-family-of-elements}}
of `b` and `a` to `C` is defined to be the type

```text
  (i : I) → C i (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

The definition of (ordinary) double lifts is somewhat simpler: Given a lift `b`
of `a : I → A` to a type family `B : A → 𝒰`, a
{{#concept "double lift" Disambiguation="families of elements" Agda=double-lift-family-of-elements}}
of `a` and `b` to a type family

```text
  C : (x : A) → B x → 𝒰
```

is a family of elements

```text
  (i : I) → C (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

The type of double lifts plays a role in the
[universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md).

## Definitions

### Dependent double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : (i : I) → A i → UU l3}
  (C : (i : I) (x : A i) → B i x → UU l4)
  {a : (i : I) → A i} (b : dependent-lift-family-of-elements B a)
  where

  dependent-double-lift-family-of-elements : UU (l1 ⊔ l4)
  dependent-double-lift-family-of-elements =
    dependent-lift-family-of-elements (λ i → C i (a i)) b
```

### Double lifts of families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {B : A → UU l3}
  (C : (x : A) → B x → UU l4)
  {a : I → A} (b : lift-family-of-elements B a)
  where

  double-lift-family-of-elements : UU (l1 ⊔ l4)
  double-lift-family-of-elements =
    dependent-lift-family-of-elements (λ i → C (a i)) b
```

## See also

- [Lifts of families of elements](orthogonal-factorization-systems.lifts-families-of-elements.md)
- [Lifts of maps](orthogonal-factorization-systems.lifts-maps.md)
- [The universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md)
