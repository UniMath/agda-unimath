# Automorphisms of types with isolated elements

```agda
module foundation.automorphisms-types-with-isolated-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.equivalences-types-with-isolated-elements
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
open import foundation.transpositions-isolated-elements
open import foundation.universe-levels

open import structured-types.pointed-equivalences
```

</details>

## Idea

Consider a type `A` equipped with an
[isolated element](foundation.isolated-elements.md) `a`, and write `C` for the
complement of `a` in `A`. Then there is an
[equivalence](foundation-core.equivalences.md)

```text
  Aut A ≃ Aut C × isolated-element A.
```

The idea behind the proof is that every automorphism `e` on A can be factored as
an equivalence that fixes the point `a` and the
[transposition](foundation.transpositions-types-with-isolated-elements.md) with
the isolated element `b := e a`. By this unique factorization result, we obtain
an equivalence

```text
  Aut A ≃ ((A , a) ≃∗ (A , a)) × isolated-element A.
```

The proof is then finished by showing that any equivalence that fixes the
isolated element `a` is uniquely determined by an automorphism on the complement
of `a`.

## Definitions

### The value of an automorphism at an isolated element, and the transposition associated to it

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  (e : A ≃ A)
  where

  value-isolated-element-equiv : isolated-element A
  value-isolated-element-equiv = map-equiv-isolated-element e (a , d)

  transposition-value-isolated-element-equiv :
    A ≃ A
  transposition-value-isolated-element-equiv =
    transposition-isolated-elements (a , d) value-isolated-element-equiv
```

### Any equivalence that fixes an isolated point is uniquely determined by its restriction to the complement

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  ((e , p) (f , q) : (A , a) ≃∗ (A , a))
  where

  htpy-equiv-complement-isolated-element :
    map-equiv-complement-isolated-element e (a , d) (a , d) p ~
    map-equiv-complement-isolated-element f (a , d) (a , d) q →
    htpy-equiv e f
  htpy-equiv-complement-isolated-element H x =
    rec-coproduct
      ( λ { refl → p ∙ inv q})
      ( λ n → ap pr1 (H (x , n)))
      ( d x)
```
