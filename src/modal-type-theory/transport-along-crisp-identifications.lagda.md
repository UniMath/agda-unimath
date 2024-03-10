# Transport along crisp identifications

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.transport-along-crisp-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
```

</details>

## Idea

Given a crisp type family `B` that depend crisply on `A`, a crisp
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A` and a
crisp element `b : B x`, we can
{{#concept "transport" Disambiguation="along crisp identifications" Agda=tr-crisp}}
the element `b` along the crisp identification `p` to obtain an element
`tr-crisp B p b : B y`.

## Definitions

### Transport along crisp identifications

```agda
@♭ tr-crisp :
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  (@♭ B : @♭ A → UU l2) {@♭ x y : A}
  (@♭ p : x ＝ y) → @♭ B x → B y
tr-crisp B refl x = x
```

## Properties

### Transport preserves concatenation of crisp identifications

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  tr-crisp-concat :
    {@♭ x y z : A} (@♭ p : x ＝ y) (@♭ q : y ＝ z) (@♭ b : B x) →
    tr-crisp B (p ∙ q) b ＝ tr-crisp B q (tr-crisp B p b)
  tr-crisp-concat p q b =
    crisp-based-ind-Id
      ( λ y q → tr-crisp B (p ∙ q) b ＝ tr-crisp B q (tr-crisp B p b))
      ( crisp-based-ind-Id
        ( λ y p → tr-crisp B (p ∙ refl) b ＝ tr-crisp B p b)
        ( refl)
        ( p))
      ( q)
```

### Transposing crisp transport along the inverse of a crisp identification

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2}
  where

  eq-transpose-tr-crisp :
    {@♭ x y : A} (@♭ p : x ＝ y) {@♭ u : B x} {@♭ v : B y} →
    @♭ v ＝ tr-crisp B p u → tr-crisp B (inv p) v ＝ u
  eq-transpose-tr-crisp p {u} {.(tr-crisp B p u)} refl =
    crisp-based-ind-Id (λ y p → tr-crisp B (inv p) (tr-crisp B p u) ＝ u) refl p

  eq-transpose-tr-crisp' :
    {@♭ x y : A} (@♭ p : x ＝ y) {@♭ u : B x} {@♭ v : B y} →
    @♭ tr-crisp B p u ＝ v → u ＝ tr-crisp B (inv p) v
  eq-transpose-tr-crisp' p {u} {.(tr-crisp B p u)} refl =
    crisp-based-ind-Id (λ y p → u ＝ tr-crisp B (inv p) (tr-crisp B p u)) refl p
```

### Every crisp family of maps preserves crisp transport

```agda
preserves-tr-crisp :
  {@♭ l1 l2 l3 : Level} {@♭ I : UU l1}
  {@♭ A : @♭ I → UU l2} {@♭ B : @♭ I → UU l3}
  (@♭ f : (@♭ i : I) → A i → B i)
  {@♭ i j : I} (@♭ p : i ＝ j) (@♭ x : A i) →
  f j (tr-crisp A p x) ＝ tr-crisp B p (f i x)
preserves-tr-crisp {A = A} {B} f {i} p x =
  crisp-based-ind-Id
    ( λ j p → f j (tr-crisp A p x) ＝ tr-crisp B p (f i x))
    ( refl)
    ( p)
```

### Transporting along the action on crisp identifications of a function

```agda
tr-crisp-ap :
  {@♭ l1 l2 l3 l4 : Level}
  {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} {@♭ C : UU l3} {@♭ D : @♭ C → UU l4}
  (@♭ f : A → C) (@♭ g : (@♭ x : A) → B x → D (f x))
  {@♭ x y : A} (@♭ p : x ＝ y) (@♭ z : B x) →
  tr-crisp D (ap f p) (g x z) ＝ g y (tr-crisp B p z)
tr-crisp-ap {A = A} {B} {C} {D} f g {x} p z =
  crisp-based-ind-Id
    ( λ y p → tr-crisp D (ap f p) (g x z) ＝ g y (tr-crisp B p z))
    ( refl)
    ( p)
```

### Computing maps out of crisp identity types as crisp transports

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : @♭ A → UU l2} {@♭ a : A}
  (@♭ f : (@♭ x : A) → @♭ (a ＝ x) → B x)
  where

  compute-map-out-of-crisp-identity-type :
    (@♭ x : A) (@♭ p : a ＝ x) → f x p ＝ tr-crisp B p (f a refl)
  compute-map-out-of-crisp-identity-type x p =
    crisp-based-ind-Id (λ x p → f x p ＝ tr-crisp B p (f a refl)) refl p
```

### Computing crisp transport in the crisp type family of crisp identifications with a fixed target

```agda
tr-crisp-Id-left :
  {@♭ l : Level} {@♭ A : UU l} {@♭ a b c : A} (@♭ q : b ＝ c) (@♭ p : b ＝ a) →
  tr-crisp (_＝ a) q p ＝ (inv q ∙ p)
tr-crisp-Id-left {a = a} q p =
  crisp-based-ind-Id (λ y q → tr-crisp (_＝ a) q p ＝ (inv q ∙ p)) refl q
```

### Computing crisp transport in the crisp type family of crisp identifications with a fixed source

```agda
tr-crisp-Id-right :
  {@♭ l : Level} {@♭ A : UU l} {@♭ a b c : A} (@♭ q : b ＝ c) (@♭ p : a ＝ b) →
  tr-crisp (a ＝_) q p ＝ (p ∙ q)
tr-crisp-Id-right {a = a} q p =
  crisp-based-ind-Id (λ y q → tr-crisp (a ＝_) q p ＝ (p ∙ q)) (inv right-unit) q
```

### Substitution law for crisp transport

```agda
substitution-law-tr-crisp :
  {@♭ l1 l2 l3 : Level} {@♭ X : UU l1} {@♭ A : UU l2} (@♭ B : @♭ A → UU l3)
  (@♭ f : X → A)
  {@♭ x y : X} (@♭ p : x ＝ y) {@♭ x' : B (f x)} →
  tr-crisp B (ap f p) x' ＝ tr-crisp (λ (@♭ x : X) → B (f x)) p x'
substitution-law-tr-crisp {X = X} B f p {x'} =
  crisp-based-ind-Id
    ( λ y p → tr-crisp B (ap f p) x' ＝ tr-crisp (λ (@♭ x : X) → B (f x)) p x')
    ( refl)
    ( p)
```
