# Irrefutably surjective maps

```agda
module logic.irrefutably-surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.irrefutable-propositions
open import foundation.postcomposition-dependent-functions
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import logic.double-negation-stable-embeddings

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

A map `f : A → B` is
{{#concept "irrefutably surjective" Agda=is-irrefutably-surjective}}, or
_dense_, if all of its [fibers](foundation-core.fibers-of-maps.md) are
[irrefutable](logic.irrefutable-propositions.md). I.e., for every `y : B`, it is
not not true that `y` has a preimage under `f`.

## Definitions

### The predicate on maps of being irrefutably surjective

```agda
is-irrefutably-surjective-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-irrefutably-surjective-Prop {B = B} f =
  Π-Prop B (double-negation-type-Prop ∘ fiber f)

is-irrefutably-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-irrefutably-surjective f = type-Prop (is-irrefutably-surjective-Prop f)

is-prop-is-irrefutably-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-irrefutably-surjective f)
is-prop-is-irrefutably-surjective f =
  is-prop-type-Prop (is-irrefutably-surjective-Prop f)

infix 5 _↠¬¬_
_↠¬¬_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠¬¬ B = Σ (A → B) is-irrefutably-surjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠¬¬ B)
  where

  map-irrefutable-surjection : A → B
  map-irrefutable-surjection = pr1 f

  is-irrefutably-surjective-map-irrefutable-surjection :
    is-irrefutably-surjective map-irrefutable-surjection
  is-irrefutably-surjective-map-irrefutable-surjection = pr2 f
```

### The type of all irrefutable surjective maps out of a type

```agda
Irrefutable-Surjection : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Irrefutable-Surjection l2 A = Σ (UU l2) (A ↠¬¬_)

module _
  {l1 l2 : Level} {A : UU l1} (f : Irrefutable-Surjection l2 A)
  where

  type-Irrefutable-Surjection : UU l2
  type-Irrefutable-Surjection = pr1 f

  irrefutable-surjection-Irrefutable-Surjection :
    A ↠¬¬ type-Irrefutable-Surjection
  irrefutable-surjection-Irrefutable-Surjection = pr2 f

  map-Irrefutable-Surjection : A → type-Irrefutable-Surjection
  map-Irrefutable-Surjection =
    map-irrefutable-surjection irrefutable-surjection-Irrefutable-Surjection

  is-irrefutably-surjective-map-Irrefutable-Surjection :
    is-irrefutably-surjective map-Irrefutable-Surjection
  is-irrefutably-surjective-map-Irrefutable-Surjection =
    is-irrefutably-surjective-map-irrefutable-surjection
      irrefutable-surjection-Irrefutable-Surjection
```

## Properties

### Any surjective map is irrefutably surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutably-surjective-is-surjective :
    {f : A → B} → is-surjective f → is-irrefutably-surjective f
  is-irrefutably-surjective-is-surjective H =
    intro-double-negation-type-trunc-Prop ∘ H

  irrefutable-surjection-surjection : (A ↠ B) → (A ↠¬¬ B)
  irrefutable-surjection-surjection =
    tot (λ _ → is-irrefutably-surjective-is-surjective)
```

### Any map that has a section is irrefutably surjective

```agda
is-irrefutably-surjective-has-section :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  section f → is-irrefutably-surjective f
is-irrefutably-surjective-has-section (g , G) b =
  intro-double-negation (g b , G b)
```

### The underlying irrefutable surjection of a retract

```agda
irrefutable-surjection-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → B ↠¬¬ A
irrefutable-surjection-retract R =
  ( map-retraction-retract R ,
    is-irrefutably-surjective-has-section (section-retract R))
```

### Any split surjective map is irrefutably surjective

```agda
is-irrefutably-surjective-is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-split-surjective f → is-irrefutably-surjective f
is-irrefutably-surjective-is-split-surjective H =
  intro-double-negation ∘ H
```

### Any equivalence is irrefutably surjective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutably-surjective-is-equiv :
    {f : A → B} → is-equiv f → is-irrefutably-surjective f
  is-irrefutably-surjective-is-equiv H =
    is-irrefutably-surjective-has-section (section-is-equiv H)

  is-irrefutably-surjective-map-equiv :
    (e : A ≃ B) → is-irrefutably-surjective (map-equiv e)
  is-irrefutably-surjective-map-equiv e =
    is-irrefutably-surjective-is-equiv (is-equiv-map-equiv e)

  irrefutable-surjection-equiv : A ≃ B → A ↠¬¬ B
  irrefutable-surjection-equiv e =
    (map-equiv e , is-irrefutably-surjective-map-equiv e)

  irrefutable-surjection-inv-equiv : B ≃ A → A ↠¬¬ B
  irrefutable-surjection-inv-equiv e =
    irrefutable-surjection-equiv (inv-equiv e)
```

### The identity function is irrefutably surjective

```agda
module _
  {l : Level} {A : UU l}
  where

  is-irrefutably-surjective-id : is-irrefutably-surjective (id {A = A})
  is-irrefutably-surjective-id a = intro-double-negation (a , refl)
```

### A (k+1)-connected map is irrefutably surjective

```agda
is-irrefutably-surjective-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {f : A → B} → is-connected-map (succ-𝕋 k) f →
  is-irrefutably-surjective f
is-irrefutably-surjective-is-connected-map k H =
  is-irrefutably-surjective-is-surjective (is-surjective-is-connected-map k H)
```

### Maps which are homotopic to irrefutably surjective maps are irrefutably surjective

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-irrefutably-surjective-htpy :
      {f g : A → B} → f ~ g →
      is-irrefutably-surjective g → is-irrefutably-surjective f
    is-irrefutably-surjective-htpy {f} {g} H K b =
      map-double-negation (map-equiv-fiber-htpy H b) (K b)

  abstract
    is-irrefutably-surjective-htpy' :
      {f g : A → B} → f ~ g →
      is-irrefutably-surjective f → is-irrefutably-surjective g
    is-irrefutably-surjective-htpy' H =
      is-irrefutably-surjective-htpy (inv-htpy H)
```

### A map that is both irrefutably surjective and a double negation stable embedding is an equivalence

```agda
abstract
  is-equiv-is-double-negation-stable-emb-is-irrefutably-surjective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-irrefutably-surjective f → is-double-negation-stable-emb f → is-equiv f
  is-equiv-is-double-negation-stable-emb-is-irrefutably-surjective H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-double-negation-stable-emb K y)
          ( is-double-negation-eliminating-map-is-double-negation-stable-emb K y
            ( H y)))
```

### The composite of irrefutably surjective maps is irrefutably surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-irrefutably-surjective-comp :
    {g : B → X} {h : A → B} →
    is-irrefutably-surjective g →
    is-irrefutably-surjective h →
    is-irrefutably-surjective (g ∘ h)
  is-irrefutably-surjective-comp {g} {h} G H x =
    map-double-negation
      ( map-inv-compute-fiber-comp g h x)
      ( is-irrefutable-Σ (G x) (H ∘ pr1))

  is-irrefutably-surjective-left-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) → f ~ g ∘ h →
    is-irrefutably-surjective g →
    is-irrefutably-surjective h →
    is-irrefutably-surjective f
  is-irrefutably-surjective-left-map-triangle f g h K G H =
    is-irrefutably-surjective-htpy K (is-irrefutably-surjective-comp G H)

  comp-irrefutable-surjection : B ↠¬¬ X → A ↠¬¬ B → A ↠¬¬ X
  comp-irrefutable-surjection (g , G) (h , H) =
    ( g ∘ h , is-irrefutably-surjective-comp G H)
```

### Functoriality of products preserves being irrefutably surjective

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-irrefutably-surjective-map-product :
    {f : A → C} {g : B → D} →
    is-irrefutably-surjective f →
    is-irrefutably-surjective g →
    is-irrefutably-surjective (map-product f g)
  is-irrefutably-surjective-map-product {f} {g} F G (c , d) =
    map-double-negation
      ( map-inv-compute-fiber-map-product f g (c , d))
      ( is-irrefutable-product (F c) (G d))

  irrefutable-surjection-product :
    (A ↠¬¬ C) → (B ↠¬¬ D) → ((A × B) ↠¬¬ (C × D))
  irrefutable-surjection-product f g =
    map-product (map-irrefutable-surjection f) (map-irrefutable-surjection g) ,
    is-irrefutably-surjective-map-product
      ( is-irrefutably-surjective-map-irrefutable-surjection f)
      ( is-irrefutably-surjective-map-irrefutable-surjection g)
```

### The composite of a surjective map before an equivalence is irrefutably surjective

```agda
is-irrefutably-surjective-left-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) {f : A → B} →
  is-irrefutably-surjective f →
  is-irrefutably-surjective (map-equiv e ∘ f)
is-irrefutably-surjective-left-comp-equiv e =
  is-irrefutably-surjective-comp (is-irrefutably-surjective-map-equiv e)
```

### The composite of a surjective map after an equivalence is irrefutably surjective

```agda
is-irrefutably-surjective-right-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-irrefutably-surjective f →
  (e : A ≃ B) →
  is-irrefutably-surjective (f ∘ map-equiv e)
is-irrefutably-surjective-right-comp-equiv H e =
  is-irrefutably-surjective-comp H (is-irrefutably-surjective-map-equiv e)
```

### If a composite is irrefutably surjective, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-irrefutably-surjective-left-factor :
    {g : B → X} (h : A → B) →
    is-irrefutably-surjective (g ∘ h) → is-irrefutably-surjective g
  is-irrefutably-surjective-left-factor {g} h GH x =
    map-double-negation (pr1 ∘ map-compute-fiber-comp g h x) (GH x)

  is-irrefutably-surjective-right-map-triangle' :
    (f : A → X) (g : B → X) (h : A → B) → g ∘ h ~ f →
    is-irrefutably-surjective f → is-irrefutably-surjective g
  is-irrefutably-surjective-right-map-triangle' f g h K F =
    is-irrefutably-surjective-left-factor h (is-irrefutably-surjective-htpy K F)

  is-irrefutably-surjective-right-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) → f ~ g ∘ h →
    is-irrefutably-surjective f → is-irrefutably-surjective g
  is-irrefutably-surjective-right-map-triangle f g h K =
    is-irrefutably-surjective-right-map-triangle' f g h (inv-htpy K)
```

### Characterization of the identity type of `A ↠¬¬ B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠¬¬ B)
  where

  htpy-irrefutable-surjection : (A ↠¬¬ B) → UU (l1 ⊔ l2)
  htpy-irrefutable-surjection g =
    map-irrefutable-surjection f ~ map-irrefutable-surjection g

  refl-htpy-irrefutable-surjection : htpy-irrefutable-surjection f
  refl-htpy-irrefutable-surjection = refl-htpy

  is-torsorial-htpy-irrefutable-surjection :
    is-torsorial htpy-irrefutable-surjection
  is-torsorial-htpy-irrefutable-surjection =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-irrefutable-surjection f))
      ( is-prop-is-irrefutably-surjective)
      ( map-irrefutable-surjection f)
      ( refl-htpy)
      ( is-irrefutably-surjective-map-irrefutable-surjection f)

  htpy-eq-irrefutable-surjection :
    (g : A ↠¬¬ B) → (f ＝ g) → htpy-irrefutable-surjection g
  htpy-eq-irrefutable-surjection .f refl = refl-htpy-irrefutable-surjection

  is-equiv-htpy-eq-irrefutable-surjection :
    (g : A ↠¬¬ B) → is-equiv (htpy-eq-irrefutable-surjection g)
  is-equiv-htpy-eq-irrefutable-surjection =
    fundamental-theorem-id
      is-torsorial-htpy-irrefutable-surjection
      htpy-eq-irrefutable-surjection

  extensionality-irrefutable-surjection :
    (g : A ↠¬¬ B) → (f ＝ g) ≃ htpy-irrefutable-surjection g
  extensionality-irrefutable-surjection g =
    ( htpy-eq-irrefutable-surjection g ,
    is-equiv-htpy-eq-irrefutable-surjection g)

  eq-htpy-irrefutable-surjection :
    (g : A ↠¬¬ B) → htpy-irrefutable-surjection g → f ＝ g
  eq-htpy-irrefutable-surjection g =
    map-inv-equiv (extensionality-irrefutable-surjection g)
```

### Characterization of the identity type of `Irrefutable-Surjection l2 A`

```agda
equiv-Irrefutable-Surjection :
  {l1 l2 l3 : Level} {A : UU l1} →
  Irrefutable-Surjection l2 A → Irrefutable-Surjection l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Irrefutable-Surjection f g =
  Σ ( type-Irrefutable-Surjection f ≃ type-Irrefutable-Surjection g)
    ( λ e →
      map-equiv e ∘ map-Irrefutable-Surjection f ~ map-Irrefutable-Surjection g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Irrefutable-Surjection l2 A)
  where

  id-equiv-Irrefutable-Surjection : equiv-Irrefutable-Surjection f f
  pr1 id-equiv-Irrefutable-Surjection = id-equiv
  pr2 id-equiv-Irrefutable-Surjection = refl-htpy

  is-torsorial-equiv-Irrefutable-Surjection :
    is-torsorial (equiv-Irrefutable-Surjection f)
  is-torsorial-equiv-Irrefutable-Surjection =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Irrefutable-Surjection f))
      ( type-Irrefutable-Surjection f , id-equiv)
      ( is-torsorial-htpy-irrefutable-surjection
        ( irrefutable-surjection-Irrefutable-Surjection f))

  equiv-eq-Irrefutable-Surjection :
    (g : Irrefutable-Surjection l2 A) → f ＝ g → equiv-Irrefutable-Surjection f g
  equiv-eq-Irrefutable-Surjection .f refl = id-equiv-Irrefutable-Surjection

  is-equiv-equiv-eq-Irrefutable-Surjection :
    (g : Irrefutable-Surjection l2 A) →
    is-equiv (equiv-eq-Irrefutable-Surjection g)
  is-equiv-equiv-eq-Irrefutable-Surjection =
    fundamental-theorem-id
      is-torsorial-equiv-Irrefutable-Surjection
      equiv-eq-Irrefutable-Surjection

  extensionality-Irrefutable-Surjection :
    (g : Irrefutable-Surjection l2 A) →
    (f ＝ g) ≃ equiv-Irrefutable-Surjection f g
  pr1 (extensionality-Irrefutable-Surjection g) =
    equiv-eq-Irrefutable-Surjection g
  pr2 (extensionality-Irrefutable-Surjection g) =
    is-equiv-equiv-eq-Irrefutable-Surjection g

  eq-equiv-Irrefutable-Surjection :
    (g : Irrefutable-Surjection l2 A) →
    equiv-Irrefutable-Surjection f g → f ＝ g
  eq-equiv-Irrefutable-Surjection g =
    map-inv-equiv (extensionality-Irrefutable-Surjection g)
```

### Postcomposition of extensions along irrefutably surjective maps by a double negation stable embedding is an equivalence

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-irrefutably-surjective-postcomp-extension-surjective-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-irrefutably-surjective f → is-double-negation-stable-emb g →
    is-irrefutably-surjective (postcomp-extension f i g)
  is-irrefutably-surjective-postcomp-extension-surjective-map f i g H K (h , L) =
    intro-double-negation
      ( ( j , N) ,
        ( eq-htpy-extension f
          ( g ∘ i)
          ( postcomp-extension f i g (j , N))
          ( h , L)
          ( M)
          ( λ a →
            ( ap
              ( concat' (g (i a)) (M (f a)))
              ( is-section-map-inv-is-equiv
                ( K (i a) (j (f a)))
                ( L a ∙ inv (M (f a))))) ∙
            ( is-section-inv-concat' (M (f a)) (L a)))))
    where

    J : (b : B) → fiber g (h b)
    J =
      apply-dependent-universal-property-irrefutable-surjection-is-irrefutably-surjective f H
        ( λ b → fiber-emb-Prop (g , K) (h b))
        ( λ a → (i a , L a))

    j : B → X
    j b = pr1 (J b)

    M : (g ∘ j) ~ h
    M b = pr2 (J b)

    N : i ~ (j ∘ f)
    N a = map-inv-is-equiv (K (i a) (j (f a))) (L a ∙ inv (M (f a)))

  is-equiv-postcomp-extension-is-irrefutably-surjective :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-irrefutably-surjective f → is-double-negation-stable-emb g →
    is-equiv (postcomp-extension f i g)
  is-equiv-postcomp-extension-is-irrefutably-surjective f i g H K =
    is-equiv-is-double-negation-stable-emb-is-irrefutably-surjective
      ( is-irrefutably-surjective-postcomp-extension-surjective-map f i g H K)
      ( is-double-negation-stable-emb-postcomp-extension f i g K)

  equiv-postcomp-extension-irrefutable-surjection :
    (f : A ↠¬¬ B) (i : A → X) (g : X ↪¬¬ Y) →
    extension (map-irrefutable-surjection f) i ≃
    extension (map-irrefutable-surjection f) (map-double-negation-stable-emb g ∘ i)
  pr1 (equiv-postcomp-extension-irrefutable-surjection f i g) =
    postcomp-extension (map-irrefutable-surjection f) i (map-double-negation-stable-emb g)
  pr2 (equiv-postcomp-extension-irrefutable-surjection f i g) =
    is-equiv-postcomp-extension-is-irrefutably-surjective
      ( map-irrefutable-surjection f)
      ( i)
      ( map-double-negation-stable-emb g)
      ( is-irrefutably-surjective-map-irrefutable-surjection f)
      ( is-double-negation-stable-emb-map-double-negation-stable-emb g)
```

### Every type that irrefutably surjects onto an irrefutable type is irrefutable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-is-irrefutably-surjective :
    {f : A → B} → is-irrefutably-surjective f → ¬¬ B → ¬¬ A
  is-irrefutable-is-irrefutably-surjective F nnb na =
    nnb (λ b → F b (λ p → na (pr1 p)))

  is-irrefutable-irrefutable-surjection :
    A ↠¬¬ B → ¬¬ B → ¬¬ A
  is-irrefutable-irrefutable-surjection f =
    is-irrefutable-is-irrefutably-surjective
      ( is-irrefutably-surjective-map-irrefutable-surjection f)
```

### The type of surjections `A ↠¬¬ B` is equivalent to the type of families `P` of irrefutable types over `B` equipped with an equivalence `A ≃ Σ B P`

> This remains to be shown.

## External links

- [TypeTopology.Density](https://martinescardo.github.io/TypeTopology/TypeTopology.Density.html)
  at TypeTopology
