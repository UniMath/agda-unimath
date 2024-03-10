# Mere logical consequences

```agda
module foundation.mere-logical-consequences where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

A type `B` is a
{{#concept "mere logical consequence" Disambiguation="types" Agda=mere-consequence}}
of the type `A` if the type of maps from `A` to `B` is
[inhabited](foundation.inhabited-types.md).

```text
  A ⇒ B := ║(A → B)║₋₁
```

## Definitions

### Mere logical consequences between types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  mere-consequence-prop : Prop (l1 ⊔ l2)
  mere-consequence-prop = trunc-Prop (A → B)

  mere-consequence : UU (l1 ⊔ l2)
  mere-consequence = type-Prop mere-consequence-prop

  is-prop-mere-consequence : is-prop mere-consequence
  is-prop-mere-consequence = is-prop-type-Prop mere-consequence-prop

  infixr 5 _⇒_
  _⇒_ : UU (l1 ⊔ l2)
  _⇒_ = mere-consequence
```

### The evaluation map on mere logical consequences

If `B` is a mere logical consequence of `A` and `A` is inhabited, then `B` is
inhabited.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-mere-consequence' : (A ⇒ B) → A → ║ B ║₋₁
  ev-mere-consequence' |f| a =
    rec-trunc-Prop (trunc-Prop B) (λ f → unit-trunc-Prop (f a)) |f|

  ev-mere-consequence : (A ⇒ B) → ║ A ║₋₁ → ║ B ║₋₁
  ev-mere-consequence |f| |a| =
    rec-trunc-Prop (trunc-Prop B) (ev-mere-consequence' |f|) (|a|)
```

### Mere logical consequence is a reflexive relation

```agda
module _
  {l : Level} (A : UU l)
  where

  refl-mere-consequence : A ⇒ A
  refl-mere-consequence = unit-trunc-Prop id
```

### Mere logical consequence is a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  trans-mere-consequence : B ⇒ C → A ⇒ B → A ⇒ C
  trans-mere-consequence |g| =
    rec-trunc-Prop
      ( mere-consequence-prop A C)
      ( λ f →
        rec-trunc-Prop
          ( mere-consequence-prop A C)
          ( λ g → unit-trunc-Prop (g ∘ f))
          ( |g|))
```

## See also

- [Mere logical equivalences](foundation.mere-logical-equivalences.md)
- [Universal quantification](foundation.universal-quantification.md) for the
  dependent variant of mere logical consequence.
