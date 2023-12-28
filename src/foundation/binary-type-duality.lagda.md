# Binary type duality

```agda
module foundation.binary-type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-spans
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.retractions
open import foundation.sections
open import foundation.spans
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-duality
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Using the principles of [type duality](foundation.type-duality.md) and
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md),
we can show that the type of spans `A <-- S --> B` is
[equivalent](foundation.equivalences.md) to the type of type-valued binary
relations `A → B → 𝓤`.

## Definitions

### The span associated to a binary relation

Given a binary relation `R : A → B → 𝒰`, we obtain a span

```text
  A <----- Σ (a : A), Σ (b : B), R a b -----> B.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : A → B → UU l3)
  where

  spanning-type-span-binary-relation : UU (l1 ⊔ l2 ⊔ l3)
  spanning-type-span-binary-relation = Σ A (λ a → Σ B (λ b → R a b))

  left-map-span-binary-relation : spanning-type-span-binary-relation → A
  left-map-span-binary-relation = pr1

  right-map-span-binary-relation : spanning-type-span-binary-relation → B
  right-map-span-binary-relation = pr1 ∘ pr2

  span-binary-relation : span (l1 ⊔ l2 ⊔ l3) A B
  pr1 span-binary-relation = spanning-type-span-binary-relation
  pr1 (pr2 span-binary-relation) = left-map-span-binary-relation
  pr2 (pr2 span-binary-relation) = right-map-span-binary-relation
```

### The binary relation associated to a span

Given a span

```text
       f       g
  A <----- S -----> B
```

we obtain the binary relation `a b ↦ Σ (s : S), (f s ＝ a) × (g s ＝ b)`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  binary-relation-span : span l3 A B → A → B → UU (l1 ⊔ l2 ⊔ l3)
  binary-relation-span S a b =
    Σ ( spanning-type-span S)
      ( λ s → (left-map-span S s ＝ a) × (right-map-span S s ＝ b))
```

## Properties

### Any span `S` is equivalent to the span associated to the binary relation associated to `S`

The construction of this equivalence of span diagrams is simply by pattern matching all the way.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (S : span l3 A B)
  where

  map-equiv-spanning-type-is-section-binary-relation-span :
    spanning-type-span S →
    spanning-type-span-binary-relation (binary-relation-span S)
  map-equiv-spanning-type-is-section-binary-relation-span s =
    ( left-map-span S s , right-map-span S s , s , refl , refl)

  map-inv-equiv-spanning-type-is-section-binary-relation-span :
    spanning-type-span-binary-relation (binary-relation-span S) →
    spanning-type-span S
  map-inv-equiv-spanning-type-is-section-binary-relation-span (a , b , s , _) =
    s

  is-section-map-inv-equiv-spanning-type-is-section-binary-relation-span :
    is-section
      ( map-equiv-spanning-type-is-section-binary-relation-span)
      ( map-inv-equiv-spanning-type-is-section-binary-relation-span)
  is-section-map-inv-equiv-spanning-type-is-section-binary-relation-span 
    ( ._ , ._ , s , refl , refl) =
    refl

  is-retraction-map-inv-equiv-spanning-type-is-section-binary-relation-span :
    is-retraction
      ( map-equiv-spanning-type-is-section-binary-relation-span)
      ( map-inv-equiv-spanning-type-is-section-binary-relation-span)
  is-retraction-map-inv-equiv-spanning-type-is-section-binary-relation-span s =
    refl

  is-equiv-map-equiv-spanning-type-is-section-binary-relation-span :
    is-equiv
      ( map-equiv-spanning-type-is-section-binary-relation-span)
  is-equiv-map-equiv-spanning-type-is-section-binary-relation-span =
    is-equiv-is-invertible
      ( map-inv-equiv-spanning-type-is-section-binary-relation-span)
      ( is-section-map-inv-equiv-spanning-type-is-section-binary-relation-span)
      ( is-retraction-map-inv-equiv-spanning-type-is-section-binary-relation-span)

  equiv-spanning-type-is-section-binary-relation-span :
    spanning-type-span S ≃
    spanning-type-span-binary-relation (binary-relation-span S)    
  pr1 equiv-spanning-type-is-section-binary-relation-span =
    map-equiv-spanning-type-is-section-binary-relation-span
  pr2 equiv-spanning-type-is-section-binary-relation-span =
    is-equiv-map-equiv-spanning-type-is-section-binary-relation-span

  equiv-is-section-binary-relation-span :
    equiv-span S (span-binary-relation (binary-relation-span S))
  pr1 equiv-is-section-binary-relation-span =
    equiv-spanning-type-is-section-binary-relation-span
  pr1 (pr2 equiv-is-section-binary-relation-span) =
    refl-htpy
  pr2 (pr2 equiv-is-section-binary-relation-span) =
    refl-htpy
```

### Any binary relation `R` is equivalent to the binary relation associated to the span associated to `R`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : A → B → UU l3)
  (a : A) (b : B)
  where

  map-equiv-binary-relation-span-binary-relation :
    R a b → binary-relation-span (span-binary-relation R) a b
  map-equiv-binary-relation-span-binary-relation r =
    ((a , b , r) , refl , refl)

  map-inv-equiv-binary-relation-span-binary-relation :
    binary-relation-span (span-binary-relation R) a b → R a b
  map-inv-equiv-binary-relation-span-binary-relation
    ((.a , .b , r) , refl , refl) =
    r

  is-section-map-inv-equiv-binary-relation-span-binary-relation :
    is-section
      ( map-equiv-binary-relation-span-binary-relation)
      ( map-inv-equiv-binary-relation-span-binary-relation)
  is-section-map-inv-equiv-binary-relation-span-binary-relation
    ((.a , .b , r) , refl , refl) =
    refl

  is-retraction-map-inv-equiv-binary-relation-span-binary-relation :
    is-retraction
      ( map-equiv-binary-relation-span-binary-relation)
      ( map-inv-equiv-binary-relation-span-binary-relation)
  is-retraction-map-inv-equiv-binary-relation-span-binary-relation r = refl

  is-equiv-map-equiv-binary-relation-span-binary-relation :
    is-equiv map-equiv-binary-relation-span-binary-relation
  is-equiv-map-equiv-binary-relation-span-binary-relation =
    is-equiv-is-invertible
      map-inv-equiv-binary-relation-span-binary-relation
      is-section-map-inv-equiv-binary-relation-span-binary-relation
      is-retraction-map-inv-equiv-binary-relation-span-binary-relation

  equiv-binary-relation-span-binary-relation :
    R a b ≃ binary-relation-span (span-binary-relation R) a b
  pr1 equiv-binary-relation-span-binary-relation =
    map-equiv-binary-relation-span-binary-relation
  pr2 equiv-binary-relation-span-binary-relation =
    is-equiv-map-equiv-binary-relation-span-binary-relation
```

## Theorem

### Binary spans are equivalent to binary relations

```agda
module _
  {l1 l2 l : Level} (A : UU l1) (B : UU l2)
  where

  is-section-binary-relation-span :
    is-section
      ( span-binary-relation {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
      ( binary-relation-span {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
  is-section-binary-relation-span S =
    inv
      ( eq-equiv-span
        ( S)
        ( span-binary-relation (binary-relation-span S))
        ( equiv-is-section-binary-relation-span S))

  is-retraction-binary-relation-span :
    is-retraction
      ( span-binary-relation {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
      ( binary-relation-span {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
  is-retraction-binary-relation-span R =
    inv
      ( eq-htpy
        ( λ a →
          eq-htpy
            ( λ b →
              eq-equiv
                ( R a b)
                ( binary-relation-span (span-binary-relation R) a b)
                ( equiv-binary-relation-span-binary-relation R a b))))

  is-equiv-span-binary-relation :
    is-equiv (span-binary-relation {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
  is-equiv-span-binary-relation =
    is-equiv-is-invertible
      ( binary-relation-span)
      ( is-section-binary-relation-span)
      ( is-retraction-binary-relation-span)

  binary-type-duality : (A → B → UU (l1 ⊔ l2 ⊔ l)) ≃ span (l1 ⊔ l2 ⊔ l) A B
  pr1 binary-type-duality = span-binary-relation
  pr2 binary-type-duality = is-equiv-span-binary-relation

  is-equiv-binary-relation-span :
    is-equiv (binary-relation-span {l3 = l1 ⊔ l2 ⊔ l} {A} {B})
  is-equiv-binary-relation-span =
    is-equiv-is-invertible
      ( span-binary-relation)
      ( is-retraction-binary-relation-span)
      ( is-section-binary-relation-span)

  inv-binary-type-duality : span (l1 ⊔ l2 ⊔ l) A B ≃ (A → B → UU (l1 ⊔ l2 ⊔ l))
  pr1 inv-binary-type-duality = binary-relation-span
  pr2 inv-binary-type-duality = is-equiv-binary-relation-span
```
