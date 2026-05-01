# Functoriality of dependent function types

```agda
module foundation.functoriality-dependent-function-types where

open import foundation-core.functoriality-dependent-function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-truncated-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equivalence-extensionality
open import foundation.function-extensionality
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

The type constructor for dependent function types acts contravariantly in its
first argument, and covariantly in its second argument.

## Properties

### An equivalence of base types and a family of equivalences induce an equivalence on dependent function types

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  (e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where

  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (is-section-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  abstract
    is-equiv-map-equiv-Π : is-equiv map-equiv-Π
    is-equiv-map-equiv-Π =
      is-equiv-comp
        ( map-Π
          ( λ a →
            ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
            ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
        ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
        ( is-equiv-precomp-Π-is-equiv
          ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
          ( B'))
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a →
            is-equiv-comp
              ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))
              ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
              ( is-equiv-map-equiv
                ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
              ( is-equiv-tr B
                ( is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  equiv-Π = (map-equiv-Π , is-equiv-map-equiv-Π)
```

#### Computing `map-equiv-Π`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  (e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where

  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    map-equiv-Π B e f h (map-equiv e a') ＝ map-equiv (f a') (h a')
  compute-map-equiv-Π h a' =
    ( ap
      ( λ t →
        tr B t
          ( map-equiv
            ( f (map-inv-equiv e (map-equiv e a')))
            ( h (map-inv-equiv e (map-equiv e a')))))
      ( coherence-map-inv-equiv e a')) ∙
    ( substitution-law-tr B (map-equiv e) (is-retraction-map-inv-equiv e a')) ∙
    ( α (map-inv-equiv e (map-equiv e a')) (is-retraction-map-inv-equiv e a'))
    where
    α :
      (x : A') (p : x ＝ a') →
      tr (B ∘ map-equiv e) p (map-equiv (f x) (h x)) ＝ map-equiv (f a') (h a')
    α x refl = refl

id-map-equiv-Π :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  map-equiv-Π B (id-equiv {A = A}) (λ a → id-equiv {A = B a}) ~ id
id-map-equiv-Π B h = eq-htpy (compute-map-equiv-Π B id-equiv (λ _ → id-equiv) h)
```

### Two maps being homotopic is equivalent to them being homotopic after pre- or postcomposition by an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  equiv-htpy-map-Π-fam-equiv :
    (e : fam-equiv B C) (f g : (a : A) → B a) →
    (f ~ g) ≃ (map-Π (map-fam-equiv e) f ~ map-Π (map-fam-equiv e) g)
  equiv-htpy-map-Π-fam-equiv e f g =
    equiv-Π-equiv-family (λ a → equiv-ap (e a) (f a) (g a))
```

### Families of truncated maps induce truncated maps on dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  abstract
    is-trunc-map-map-Π :
      (k : 𝕋) (f : (i : I) → A i → B i) →
      ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
    is-trunc-map-map-Π k f H h =
      is-trunc-equiv' k
        ( (i : I) → fiber (f i) (h i))
        ( compute-fiber-map-Π f h)
        ( is-trunc-Π k (λ i → H i (h i)))

  abstract
    is-emb-map-Π :
      {f : (i : I) → A i → B i} → ((i : I) → is-emb (f i)) → is-emb (map-Π f)
    is-emb-map-Π {f} H =
      is-emb-is-prop-map
        ( is-trunc-map-map-Π neg-one-𝕋 f (λ i → is-prop-map-is-emb (H i)))

  emb-Π : ((i : I) → A i ↪ B i) → ((i : I) → A i) ↪ ((i : I) → B i)
  emb-Π f = (map-Π (map-emb ∘ f) , is-emb-map-Π (is-emb-map-emb ∘ f))
```

### A family of truncated maps over any map induces a truncated map on dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  is-trunc-map-map-Π' :
    (k : 𝕋) {l4 : Level} {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
    ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
  is-trunc-map-map-Π' k {J = J} α f H h =
    is-trunc-equiv' k
      ( (j : J) → fiber (f (α j)) (h j))
      ( compute-fiber-map-Π' α f h)
      ( is-trunc-Π k (λ j → H (α j) (h j)))

  is-trunc-map-is-trunc-map-map-Π'-lzero :
    (k : 𝕋) (f : (i : I) → A i → B i) →
    ({J : UU lzero} (α : J → I) → is-trunc-map k (map-Π' α f)) →
    (i : I) → is-trunc-map k (f i)
  is-trunc-map-is-trunc-map-map-Π'-lzero k f H i b =
    is-trunc-equiv' k
      ( fiber (map-Π (λ _ → f i)) (point b))
      ( equiv-Σ
        ( λ a → f i a ＝ b)
        ( equiv-universal-property-unit (A i))
        ( λ h →
          equiv-ap
            ( equiv-universal-property-unit (B i))
            ( map-Π (λ _ → f i) h)
            ( point b)))
      ( H (λ _ → i) (point b))

  is-trunc-map-is-trunc-map-map-Π' :
    (k : 𝕋) (f : (i : I) → A i → B i) →
    ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
    (i : I) → is-trunc-map k (f i)
  is-trunc-map-is-trunc-map-map-Π' k f H i b =
    is-trunc-map-is-trunc-map-map-Π'-lzero k f H i b

  is-emb-map-Π' :
    {l4 : Level} {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
    ((i : I) → is-emb (f i)) → is-emb (map-Π' α f)
  is-emb-map-Π' α f H =
    is-emb-is-prop-map
      ( is-trunc-map-map-Π' neg-one-𝕋 α f (λ i → is-prop-map-is-emb (H i)))
```

### The action on homotopies of equivalences

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  where

  HTPY-map-equiv-Π :
    (e e' : A' ≃ A) → htpy-equiv e e' → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  HTPY-map-equiv-Π e e' H =
    (f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
    (f' : (a' : A') → B' a' ≃ B (map-equiv e' a')) →
    (K : (a' : A') → tr B (H a') ∘ map-equiv (f a') ~ map-equiv (f' a')) →
    map-equiv-Π B e f ~ map-equiv-Π B e' f'

  htpy-map-equiv-Π-refl-htpy :
    (e : A' ≃ A) → HTPY-map-equiv-Π e e (refl-htpy-equiv e)
  htpy-map-equiv-Π-refl-htpy e f f' K =
    ( htpy-map-Π
      ( λ a →
        ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a)) ·l
        ( K (map-inv-is-equiv (is-equiv-map-equiv e) a)))) ·r
    ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')

  abstract
    htpy-map-equiv-Π :
      (e e' : A' ≃ A) (H : htpy-equiv e e') → HTPY-map-equiv-Π e e' H
    htpy-map-equiv-Π e =
      ind-htpy-equiv e
        ( HTPY-map-equiv-Π e)
        ( htpy-map-equiv-Π-refl-htpy e)

    compute-htpy-map-equiv-Π :
      (e : A' ≃ A) →
      htpy-map-equiv-Π e e (refl-htpy-equiv e) ＝ htpy-map-equiv-Π-refl-htpy e
    compute-htpy-map-equiv-Π e =
      compute-ind-htpy-equiv e
        ( HTPY-map-equiv-Π e)
        ( htpy-map-equiv-Π-refl-htpy e)
```

### The action on automorphisms

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a))
  where

  map-automorphism-Π : ((a : A) → B a) → ((a : A) → B a)
  map-automorphism-Π =
    ( map-Π (λ a → (map-inv-is-equiv (is-equiv-map-equiv (f a))))) ∘
    ( precomp-Π (map-equiv e) B)

  abstract
    is-equiv-map-automorphism-Π :
      is-equiv map-automorphism-Π
    is-equiv-map-automorphism-Π =
      is-equiv-comp _ _
        ( is-equiv-precomp-Π-is-equiv (is-equiv-map-equiv e) B)
        ( is-equiv-map-Π-is-fiberwise-equiv
          ( λ a → is-equiv-map-inv-is-equiv (is-equiv-map-equiv (f a))))

  automorphism-Π : ((a : A) → B a) ≃ ((a : A) → B a)
  automorphism-Π = (map-automorphism-Π , is-equiv-map-automorphism-Π)
```

### Families of retracts induce retracts of dependent function types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  retract-Π-retract-family :
    (r : (i : I) → A i retract-of B i) →
    ((i : I) → A i) retract-of ((i : I) → B i)
  retract-Π-retract-family r =
    ( map-Π (inclusion-retract ∘ r) ,
      retraction-map-Π-fiberwise-retraction (retraction-retract ∘ r))
```

## See also

- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
- Functorial properties of function types are recorded in
  [`foundation.functoriality-function-types`](foundation.functoriality-function-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
