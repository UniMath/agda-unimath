# Lawvere's fixed point theorem

```agda
module foundation.lawveres-fixed-point-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-extensionality-axiom
open import foundation.propositional-truncations
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

{{#concept "Lawvere's fixed point theorem" Agda=fixed-point-theorem-Lawvere WD="Lawvere's fixed-point theorem" WDID=Q15809744}}
asserts that if there is a [surjective map](foundation.surjective-maps.md)
`A → (A → B)`, then any map `B → B` must have a
[fixed point](foundation.fixed-points-endofunctions.md).

## Theorem

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → A → B}
  where

  abstract
    fixed-point-theorem-Lawvere :
      is-surjective f → (h : B → B) → exists-structure B (λ b → h b ＝ b)
    fixed-point-theorem-Lawvere H h =
      apply-universal-property-trunc-Prop
        ( H g)
        ( exists-structure-Prop B (λ b → h b ＝ b))
        ( λ (x , p) → intro-exists (f x x) (inv (htpy-eq p x)))
      where
      g : A → B
      g a = h (f a a)
```

## See also

- Lawvere's fixed point theorem generalizes
  [Cantor's theorem](foundation.cantors-theorem.md) in the following way: When
  `B` is the universe of
  [decidable propositions](foundation-core.decidable-propositions.md) or the
  universe of all [propositions](foundation-core.propositions.md), then we have
  an operator `B → B` with no fixed points, namely
  [negation](foundation-core.negation.md). Since `𝒫(A) = (A → Prop)`, It follows
  that there can be no surjection `A ↠ 𝒫(A)`.

## External links

- [Lawvere's fixed point theorem](https://ncatlab.org/nlab/show/Lawvere%27s+fixed+point+theorem)
  at $n$Lab
- [Lawvere's fixed-point theorem](https://en.wikipedia.org/wiki/Lawvere%27s_fixed-point_theorem)
  at Wikipedia
