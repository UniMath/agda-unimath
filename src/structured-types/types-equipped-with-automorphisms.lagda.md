# Types equipped with automorphisms

```agda
module structured-types.types-equipped-with-automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

A {{#concept "type equipped with an automorphism" Agda=Type-With-Automorphism}}
is a pair consisting of a type `A` and an
[automorphism](foundation.automorphisms.md) on `e : A ≃ A`.

## Definitions

### Types equipped with automorphisms

```agda
Type-With-Automorphism : (l : Level) → UU (lsuc l)
Type-With-Automorphism l = Σ (UU l) (Aut)

module _
  {l : Level} (A : Type-With-Automorphism l)
  where

  type-Type-With-Automorphism : UU l
  type-Type-With-Automorphism = pr1 A

  automorphism-Type-With-Automorphism : Aut type-Type-With-Automorphism
  automorphism-Type-With-Automorphism = pr2 A

  map-Type-With-Automorphism :
    type-Type-With-Automorphism → type-Type-With-Automorphism
  map-Type-With-Automorphism = map-equiv automorphism-Type-With-Automorphism

  type-with-endomorphism-Type-With-Automorphism : Type-With-Endomorphism l
  pr1 type-with-endomorphism-Type-With-Automorphism =
    type-Type-With-Automorphism
  pr2 type-with-endomorphism-Type-With-Automorphism =
    map-Type-With-Automorphism
```

### Types equipped with the identity automorphism

```agda
trivial-Type-With-Automorphism : {l : Level} → UU l → Type-With-Automorphism l
pr1 (trivial-Type-With-Automorphism X) = X
pr2 (trivial-Type-With-Automorphism X) = id-equiv
```

## See also

- Sets equipped with automorphisms are defined in
  [`structured-types.sets-equipped-with-automorphisms`](structured-types.sets-equipped-with-automorphisms.md)
- Cyclic types are
  [sets equipped with automorphisms](structured-types.sets-equipped-with-automorphisms.md)
  of which the automorphism acts transitively.
- The
  [descent property of the circle](synthetic-homotopy-theory.descent-circle.md)
  shows that type families over the
  [circle](synthetic-homotopy-theory.circle.md) are
  [equivalently](foundation.equivalences.md) described as types equipped with
  automorphisms.
