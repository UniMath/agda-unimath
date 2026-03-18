# The universal property of freely generated algebras

```agda
module universal-algebra.universal-property-freely-generated-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.signatures
```

</details>

## Idea

The universal property of a freely generated
[algebra](universal-algebra.algebras.md) `A` for an
[algebraic theory](universal-algebra.algebraic-theories.md) `T` with generator
type `G` is that for all algebras `B` for `T`, the type of maps `G → B` is
[equivalent](foundation.equivalences.md) to the type of
[homomorphisms](universal-algebra.homomorphisms-of-algebras.md) from `A` to `B`.

## Definition

```agda
is-free-Algebra :
  {l1 l2 l3 l4 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (G : UU l3)
  (A : Algebra l4 σ T) →
  UUω
is-free-Algebra σ T G A =
  {l5 : Level} (B : Algebra l5 σ T) →
  (G → type-Algebra σ T B) ≃ hom-Algebra σ T A B
```
