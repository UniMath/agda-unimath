# Reflecting homomorphisms of congruences

```agda
module universal-algebra.reflecting-homomorphisms-congruences where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalence-relations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.subtypes
open import foundation.universe-levels

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

A [homomorphism](universal-algebra.homomorphisms-of-algebras.md) `φ` from an
[algebra](universal-algebra.algebras.md) `A` to an algebra in the same
[theory](universal-algebra.algebraic-theories.md) `B` is said to reflect an
[equivalence relation](foundation.equivalence-relations.md) on `A` if whenever
`a₁ a₂ : A` are similar relative to the equivalence relation, `φ a₁ = φ b₂`.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R : equivalence-relation l4 (type-Algebra σ T A))
  (B : Algebra l5 σ T)
  where

  reflects-equivalence-relation-prop-hom-Algebra :
    subtype (l3 ⊔ l4 ⊔ l5) (hom-Algebra σ T A B)
  reflects-equivalence-relation-prop-hom-Algebra φ =
    reflects-prop-equivalence-relation
      ( R)
      ( set-Algebra σ T B)
      ( map-hom-Algebra σ T A B φ)

  reflects-equivalence-relation-hom-Algebra :
    hom-Algebra σ T A B → UU (l3 ⊔ l4 ⊔ l5)
  reflects-equivalence-relation-hom-Algebra =
    is-in-subtype reflects-equivalence-relation-prop-hom-Algebra

  is-prop-reflects-equivalence-relation-hom-Algebra :
    (φ : hom-Algebra σ T A B) →
    is-prop (reflects-equivalence-relation-hom-Algebra φ)
  is-prop-reflects-equivalence-relation-hom-Algebra =
    is-prop-is-in-subtype reflects-equivalence-relation-prop-hom-Algebra

  reflecting-equivalence-relation-hom-Algebra : UU (l1 ⊔ l3 ⊔ l4 ⊔ l5)
  reflecting-equivalence-relation-hom-Algebra =
    type-subtype reflects-equivalence-relation-prop-hom-Algebra

reflecting-congruence-hom-Algebra :
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T) →
  congruence-Algebra l4 σ T A → Algebra l5 σ T → UU (l1 ⊔ l3 ⊔ l4 ⊔ l5)
reflecting-congruence-hom-Algebra σ T A R =
  reflecting-equivalence-relation-hom-Algebra
    ( σ)
    ( T)
    ( A)
    ( equivalence-relation-congruence-Algebra σ T A R)
```
