# Injective maps

```agda
module foundation.injective-maps where

open import foundation-core.injective-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → B` is **injective**, also called _left cancellable_, if
`f x ＝ f y` implies `x ＝ y`.

## Warning

The notion of injective map is, however, not homotopically coherent. It is fine
to use injectivity for maps between [sets](foundation-core.sets.md), but for
maps between general types it is recommended to use the notion of
[embedding](foundation-core.embeddings.md).

## Definitions

### Noninjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-not-injective : (A → B) → UU (l1 ⊔ l2)
  is-not-injective f = ¬ (is-injective f)
```

### Any map out of an empty type is injective

```agda
is-injective-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-empty A → is-injective f
is-injective-is-empty f is-empty-A {x} = ex-falso (is-empty-A x)
```

### Any injective map between sets is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-is-injective' :
      (is-set-A : is-set A) (is-set-B : is-set B) (f : A → B) →
      is-injective f → is-emb f
    is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
      is-equiv-has-converse-is-prop
        ( is-set-A x y)
        ( is-set-B (f x) (f y))
        ( is-injective-f)

    is-emb-is-injective :
      {f : A → B} → is-set B → is-injective f → is-emb f
    is-emb-is-injective {f} H I =
      is-emb-is-injective' (is-set-is-injective H I) H f I

    is-prop-map-is-injective :
      {f : A → B} → is-set B → is-injective f → is-prop-map f
    is-prop-map-is-injective {f} H I =
      is-prop-map-is-emb (is-emb-is-injective H I)

emb-injection :
  {l1 l2 : Level} {A : UU l1} (B : Set l2) →
  injection A (type-Set B) → A ↪ (type-Set B)
emb-injection B = tot (λ f → is-emb-is-injective (is-set-type-Set B))
```

### For a map between sets, being injective is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-injective :
    is-set A → (f : A → B) → is-prop (is-injective f)
  is-prop-is-injective H f =
    is-prop-implicit-Π
      ( λ x → is-prop-implicit-Π (λ y → is-prop-function-type (H x y)))

  is-injective-Prop : is-set A → (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-injective-Prop H f) = is-injective f
  pr2 (is-injective-Prop H f) = is-prop-is-injective H f
```

### The map on total spaces induced by a family of injective maps is an injective map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where
  is-injective-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-injective (f x)) →
    is-injective (tot f)
  is-injective-tot {f} H {x} {y} p =
    eq-pair-Σ
      ( ap pr1 p)
      ( H (pr1 y) (preserves-tr f (ap pr1 p) (pr2 x) ∙ tr-eq-Σ p))

  injection-tot : ((x : A) → injection (B x) (C x)) → injection (Σ A B) (Σ A C)
  injection-tot f = (tot (pr1 ∘ f) , is-injective-tot (pr2 ∘ f))
```

### Families of injective maps induce injective maps on dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  abstract
    is-injective-map-Π :
      {f : (i : I) → A i → B i} →
      ((i : I) → is-injective (f i)) → is-injective (map-Π f)
    is-injective-map-Π {f = f} H {x} {y} p = eq-htpy (λ i → H i (htpy-eq p i))

  injection-Π :
    ((i : I) → injection (A i) (B i)) →
    injection ((i : I) → A i) ((i : I) → B i)
  injection-Π f = (map-Π (pr1 ∘ f) , is-injective-map-Π (pr2 ∘ f))
```

## See also

- [Embeddings](foundation-core.embeddings.md)
- [Path-cosplit maps](foundation.path-cosplit-maps.md)
