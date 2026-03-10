# Set quotients of finite sequences

```agda
module lists.set-quotients-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.dependent-products-equivalence-relations
open import foundation.effective-maps-equivalence-relations
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations
open import foundation-core.equivalences

open import lists.finite-sequences
open import lists.functoriality-finite-sequences

open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Let `Xⁿ` be the type of [finite sequences](lists.finite-sequences.md) of length
`n` of values of `X`, and given an
[equivalence relation](foundation.equivalence-relations.md) `R` on a type `A`,
let `Rⁿ` be the
[induced equivalence relation](foundation.dependent-products-equivalence-relations.md)
on `Aⁿ`. Then the [set quotient](foundation.set-quotients.md) `Aⁿ/Rⁿ` is
[equivalent](foundation-core.equivalences.md) to `(A/R)ⁿ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : equivalence-relation l2 A)
  (n : ℕ)
  where

  equivalence-relation-fin-sequence :
    equivalence-relation l2 (fin-sequence A n)
  equivalence-relation-fin-sequence =
    Π-equivalence-relation (Fin n) (λ _ → R)

  reflects-equivalence-relation-map-quotient-map-fin-sequence :
    reflects-equivalence-relation
      ( equivalence-relation-fin-sequence)
      ( map-fin-sequence n (quotient-map R))
  reflects-equivalence-relation-map-quotient-map-fin-sequence {x} {y} x~y =
    eq-htpy (λ i → apply-effectiveness-quotient-map' R (x~y i))

  reflecting-map-equivalence-relation-fin-sequence :
    reflecting-map-equivalence-relation
      ( equivalence-relation-fin-sequence)
      ( fin-sequence (set-quotient R) n)
  reflecting-map-equivalence-relation-fin-sequence =
    ( map-fin-sequence n (quotient-map R) ,
      reflects-equivalence-relation-map-quotient-map-fin-sequence)

  abstract
    is-surjective-map-quotient-map-fin-sequence :
      is-surjective (map-fin-sequence n (quotient-map R))
    is-surjective-map-quotient-map-fin-sequence f =
      map-trunc-Prop
        ( λ g → (pr1 ∘ g , eq-htpy (pr2 ∘ g)))
        ( finite-choice-Fin n (λ i → is-surjective-quotient-map R (f i)))

    is-effective-map-quotient-map-fin-sequence :
      is-effective
        ( equivalence-relation-fin-sequence)
        ( map-fin-sequence n (quotient-map R))
    is-effective-map-quotient-map-fin-sequence x y =
      equiv-iff
        ( Id-Prop
          ( function-Set (Fin n) (quotient-Set R))
          ( map-fin-sequence n (quotient-map R) x)
          ( map-fin-sequence n (quotient-map R) y))
        ( prop-equivalence-relation equivalence-relation-fin-sequence x y)
        ( λ qx=qy i → apply-effectiveness-quotient-map R (htpy-eq qx=qy i))
        ( λ Rxy → eq-htpy (λ i → apply-effectiveness-quotient-map' R (Rxy i)))

    is-set-quotient-fin-sequence-set-quotient :
      is-set-quotient
        ( equivalence-relation-fin-sequence)
        ( function-Set (Fin n) (quotient-Set R))
        ( reflecting-map-equivalence-relation-fin-sequence)
    is-set-quotient-fin-sequence-set-quotient =
      is-set-quotient-is-surjective-and-effective
        ( equivalence-relation-fin-sequence)
        ( function-Set (Fin n) (quotient-Set R))
        ( reflecting-map-equivalence-relation-fin-sequence)
        ( is-surjective-map-quotient-map-fin-sequence ,
          is-effective-map-quotient-map-fin-sequence)

    equiv-fin-sequence-set-quotient :
      set-quotient equivalence-relation-fin-sequence ≃
      fin-sequence (set-quotient R) n
    equiv-fin-sequence-set-quotient =
      equiv-uniqueness-set-quotient-set-quotient
        ( equivalence-relation-fin-sequence)
        ( function-Set (Fin n) (quotient-Set R))
        ( reflecting-map-equivalence-relation-fin-sequence)
        ( is-set-quotient-fin-sequence-set-quotient)
```
