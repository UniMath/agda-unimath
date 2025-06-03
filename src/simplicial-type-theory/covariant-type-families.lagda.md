# Covariant type families

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.covariant-type-families
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.families-of-types-local-at-maps
open import orthogonal-factorization-systems.null-types

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

A type family `B : A → 𝒰` is
{{#concept "(simplicially) covariant" Disambiguation="type family" Agda=is-simplicially-covariant}}
if one of the following equivalent conditions hold:

1. For every directed edge `f : x →▵ y` in `A` and element `x'` over `x`, the
   type of dependent directed edges over `f` based at `x'` is
   [torsorial](foundation.torsorial-type-families.md).

2. For every simplicial arrow `α` in `A`, and element `x'` over `α 0▵`, the type
   of dependent directed edges over `α` based at `x'` is torsorial.

   ```text
     (α : arrow A) (x' : B (α 0▵)) →
     is-contr (Σ (y' : B (α 1▵)), (dependent-hom B α x' y'))
   ```

   Note that this is just a slight simplification of the previous condition.

3. The type family is
   [local](orthogonal-factorization-systems.local-type-families.md) at the left
   end-point inclusion `0▵ : 1 ↪ Δ¹`.

4. The following square is a [pullback](foundation-core.pullbacks.md)

   ```text
                            postcomp Δ¹ pr1
    (Δ¹ → Σ (x : A), (B x)) ---------------> (Δ¹ → A)
              |                                |
              |                                |
        ev 0▵ |                                | ev 0▵
              |                                |
              ∨                                ∨
         Σ (x : A), (B x) -------------------> A
                                pr1
   ```

## Definitions

### The predicate on type families of being simplicially covariant

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-simplicially-covariant : UU (I1 ⊔ l1 ⊔ l2)
  is-simplicially-covariant = is-local-family (point 0▵) B
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-simplicially-covariant' : UU (I1 ⊔ l1 ⊔ l2)
  is-simplicially-covariant' =
    (α : arrow▵ A) (x' : B (α 0▵)) →
    is-torsorial (dependent-hom▵ B (hom▵-arrow▵ α) x')
```

## References

{{#bibliography}} {{#reference RS17}}
