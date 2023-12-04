# Lifts of families of elements

```agda
module foundation.lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Consider a family of elements `a : (i : I) → A i` and a type family

```text
  B : (i : I) → A i → 𝒰.
```

A {{#concept "dependent lift" Disambiguation="family of elements"}} of the
family of elements `a` to the type family `B` is a family of elements

```text
  (i : I) → B i (a i).
```

An important special case occurs when `a : I → A` is a family of elements of a
fixed type `A`, and `B` is a type family over `A`. In this case, a
{{#concept "lift" Disambiguation="family of elements"}} of the family of
elements `a` is a family of elements

```text
  (i : I) → B (a i).
```

## Definitions

### Dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  (B : (i : I) → A i → UU l3)
  where

  dependent-lift-family-of-elements : UU (l1 ⊔ l3)
  dependent-lift-family-of-elements = (i : I) → B i (a i)
```

### Lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A) (B : A → UU l3)
  where

  lift-family-of-elements : UU (l1 ⊔ l3)
  lift-family-of-elements = dependent-lift-family-of-elements a (λ _ → B)
```

### Dependent lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  {B : (i : I) → A i → UU l3} (C : (i : I) (x : A i) → B i x → UU l4)
  where

  dependent-lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  dependent-lift-binary-family-of-elements =
    dependent-lift-family-of-elements a (λ i x → (y : B i x) → C i x y)
```

### Lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  {B : A → UU l3} {C : (x : A) → B x → UU l4}
  where

  lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  lift-binary-family-of-elements =
    dependent-lift-binary-family-of-elements a (λ _ → C)
```

### Dependent double lifts of families of elements

Given a lift `b` of `a : (i : I) → A i` to a type family
`B : (i : I) → A i → 𝒰`, a
{{#concept "dependent double lift" Disambiguation="families of elements"}} of
`a` and `b` to a type family

```text
  C : (i : I) (x : A i) → B i x → 𝒰
```

is a family of elements

```text
  (i : I) → C i (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {a : (i : I) → A i}
  {B : (i : I) → A i → UU l3} (b : dependent-lift-family-of-elements a B)
  (C : (i : I) (x : A i) → B i x → UU l4)
  where

  dependent-double-lift-family-of-elements : UU (l1 ⊔ l4)
  dependent-double-lift-family-of-elements =
    dependent-lift-family-of-elements b (λ i → C i (a i))
```

### Double lifts of families of elements

Given a lift `b` of `a : I → A` to a type family `B : A → 𝒰`, a
{{#concept "double lift" Disambiguation="families of elements"}} of `a` and `b`
to a type family

```text
  C : (x : A) → B x → 𝒰
```

is a family of elements

```text
  (i : I) → C (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} {a : I → A}
  {B : A → UU l3} (b : lift-family-of-elements a B) (C : (x : A) → B x → UU l4)
  where

  double-lift-family-of-elements : UU (l1 ⊔ l4)
  double-lift-family-of-elements =
    dependent-lift-family-of-elements b (λ i → C (a i))
```
