# Lifts of families of elements

```agda
module orthogonal-factorization-systems.lifts-families-of-elements where
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

## See also

- [Double lifts of families of elements](orthogonal-factorization-systems.double-lifts-families-of-elements.md)
- [Lifts of maps](orthogonal-factorization-systems.lifts-of-maps.md)
