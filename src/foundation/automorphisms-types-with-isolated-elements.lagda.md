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
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isolated-elements
open import foundation.negated-equality
open import foundation.negation
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

### Any equivalence that fixes an isolated point is uniquely determined by its restriction to the complement

```agda
module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  (e : (A , a) ≃∗ (A , a))
  where

  equiv-complement-isolated-element :
    complement-isolated-element (a , d) ≃ complement-isolated-element (a , d)
  equiv-complement-isolated-element =
    equiv-Σ
      ( λ x → a ≠ x)
      ( equiv-pointed-equiv e)
      ( λ x →
        equiv-neg
          ( equiv-concat (inv (preserves-point-pointed-equiv e)) _ ∘e
            equiv-ap (equiv-pointed-equiv e) a x))

  map-equiv-complement-isolated-element :
    complement-isolated-element (a , d) → complement-isolated-element (a , d)
  map-equiv-complement-isolated-element =
    map-equiv equiv-complement-isolated-element

module _
  {l1 : Level} {A : UU l1} ((a , d) : isolated-element A)
  (e f : (A , a) ≃∗ (A , a))
  where

  htpy-equiv-complement-isolated-element :
    map-equiv-complement-isolated-element (a , d) e ~
    map-equiv-complement-isolated-element (a , d) f →
    htpy-equiv (equiv-pointed-equiv e) (equiv-pointed-equiv f)
  htpy-equiv-complement-isolated-element H x =
    rec-coproduct
      ( λ { refl →
            preserves-point-pointed-equiv e ∙
            inv (preserves-point-pointed-equiv f)})
      ( λ n → ap pr1 (H (x , n)))
      ( d x)
```
