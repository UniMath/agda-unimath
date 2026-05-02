# Decidable type families

```agda
module foundation.decidable-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
-- open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-dense-equality
open import foundation.irrefutable-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B : A → 𝒰` is said to be
{{#concept "decidable" Disambiguation="type family" Agda=is-decidable-family}}
if we can for every `x : A` either construct an element of `B x` or we can prove
that it is [empty](foundation-core.empty-types.md). In other words, we interpret
decidability via the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory. A related concept is that a type family is either
[inhabited](foundation.inhabited-types.md) or empty, where inhabitedness of a
type is expressed using the
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### The Curry–Howard interpretation of decidability

```agda
is-decidable-family : {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-family {A = A} P = (x : A) → is-decidable (P x)

decidable-family : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
decidable-family l2 A = Σ (A → UU l2) is-decidable-family

module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-family l2 A)
  where

  family-decidable-family : A → UU l2
  family-decidable-family = pr1 P

  is-decidable-decidable-family : is-decidable-family family-decidable-family
  is-decidable-decidable-family = pr2 P
```

## Properties

### Base change of decidable type families

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (P : decidable-family l3 B)
  where

  base-change-decidable-family : (f : A → B) → decidable-family l3 A
  base-change-decidable-family f =
    ( family-decidable-family P ∘ f , is-decidable-decidable-family P ∘ f)
```

### The negation of a decidable family is decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-family l2 A)
  where

  is-decidable-neg-decidable-family :
    is-decidable-family (λ x → ¬ (family-decidable-family P x))
  is-decidable-neg-decidable-family =
    is-decidable-neg ∘ is-decidable-decidable-family P

  neg-decidable-family : decidable-family l2 A
  neg-decidable-family =
    ( ( λ x → ¬ (family-decidable-family P x)) ,
      is-decidable-neg-decidable-family)
```

### Composition of decidable families

Given a decidable family of types with double negation dense equality
`P : A → 𝒰` and a decidable type family `Q : (x : A) → P x → 𝒰` then, via
[type duality](foundation.type-duality.md) we may _compose_ `Q` after `P` and
obtain a decidable type family `Q ∘ P : A → 𝒰`, defined on elements as
[dependent pair types](foundation.dependent-pair-types.md).

```text
  (Q ∘ P) x := Σ (y : P x), (Q x y).
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  is-decidable-comp-decidable-family-has-double-negation-dense-equality :
    (P : decidable-family l2 A)
    (Q : (x : A) → decidable-family l3 (family-decidable-family P x)) →
    ( (x : A) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    is-decidable-family
      ( λ x → Σ (family-decidable-family P x) (family-decidable-family (Q x)))
  is-decidable-comp-decidable-family-has-double-negation-dense-equality
    P Q H x =
    rec-coproduct
      ( λ p →
        rec-coproduct
          ( λ q → inl (p , q))
          (λ nq →
            inr
              ( λ q →
                H ( x)
                  ( p)
                  ( pr1 q)
                  ( λ r →
                    nq (tr (family-decidable-family (Q x)) (inv r) (pr2 q)))))
          ( is-decidable-decidable-family (Q x) p))
      ( λ np → inr (map-neg pr1 np))
      ( is-decidable-decidable-family P x)

  comp-decidable-family-has-double-negation-dense-equality :
    (P : decidable-family l2 A) →
    ( (x : A) → decidable-family l3 (family-decidable-family P x)) →
    ( (x : A) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    decidable-family (l2 ⊔ l3) A
  comp-decidable-family-has-double-negation-dense-equality P Q H =
    ( λ x → Σ (family-decidable-family P x) (family-decidable-family (Q x))) ,
    ( is-decidable-comp-decidable-family-has-double-negation-dense-equality
      ( P)
      ( Q)
      ( H))
```

## See also

- [Uniformly decidable type families](foundation.uniformly-decidable-type-families.md)
