# Functoriality of dependent function types

```agda
module foundation.functoriality-dependent-function-types where

open import foundation-core.functoriality-dependent-function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.transport
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
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
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) (f : (a' : A') → B' a' ≃ B (map-equiv e a'))
  where

  map-equiv-Π : ((a' : A') → B' a') → ((a : A) → B a)
  map-equiv-Π =
    ( map-Π
      ( λ a →
        ( tr B (is-section-map-inv-equiv e a)) ∘
        ( map-equiv (f (map-inv-equiv e a))))) ∘
    ( precomp-Π (map-inv-equiv e) B')

  compute-map-equiv-Π :
    (h : (a' : A') → B' a') (a' : A') →
    map-equiv-Π h (map-equiv e a') ＝ map-equiv (f a') (h a')
  compute-map-equiv-Π h a' =
    ( ap
      ( λ t →
        tr B t
          ( map-equiv
            ( f (map-inv-equiv e (map-equiv e a')))
            ( h (map-inv-equiv e (map-equiv e a')))))
      ( coherence-map-inv-equiv e a')) ∙
    ( ( tr-ap
        ( map-equiv e)
        ( λ _ → id)
        ( is-retraction-map-inv-equiv e a')
        ( map-equiv
          ( f (map-inv-equiv e (map-equiv e a')))
          ( h (map-inv-equiv e (map-equiv e a'))))) ∙
      ( α ( map-inv-equiv e (map-equiv e a'))
          ( is-retraction-map-inv-equiv e a')))
    where
    α :
      (x : A') (p : x ＝ a') →
      tr (B ∘ map-equiv e) p (map-equiv (f x) (h x)) ＝ map-equiv (f a') (h a')
    α x refl = refl

  abstract
    is-equiv-map-equiv-Π : is-equiv map-equiv-Π
    is-equiv-map-equiv-Π =
      is-equiv-comp
        ( map-Π (λ a →
          ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a)) ∘
          ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))))
        ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')
        ( is-equiv-precomp-Π-is-equiv
          ( map-inv-is-equiv (is-equiv-map-equiv e))
          ( is-equiv-map-inv-is-equiv (is-equiv-map-equiv e))
          ( B'))
        ( is-equiv-map-Π _
          ( λ a → is-equiv-comp
            ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))
            ( map-equiv (f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
            ( is-equiv-map-equiv
              ( f (map-inv-is-equiv (is-equiv-map-equiv e) a)))
            ( is-equiv-tr B
              ( is-section-map-inv-is-equiv (is-equiv-map-equiv e) a))))

  equiv-Π : ((a' : A') → B' a') ≃ ((a : A) → B a)
  pr1 equiv-Π = map-equiv-Π
  pr2 equiv-Π = is-equiv-map-equiv-Π
```

### The functorial action of dependent function types preserves identity morphisms

```agda
id-map-equiv-Π :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  ( map-equiv-Π B (id-equiv {A = A}) (λ a → id-equiv {A = B a})) ~ id
id-map-equiv-Π B h = eq-htpy (compute-map-equiv-Π B id-equiv (λ a → id-equiv) h)
```

### The fibers of `map-Π'`

```agda
equiv-fib-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fib (f (α j)) (h j)) ≃ fib (map-Π' α f) h
equiv-fib-map-Π' α f h =
  equiv-tot (λ x → equiv-eq-htpy) ∘e distributive-Π-Σ
```

### Truncated families of maps induce truncated maps on dependent function types

```agda
abstract
  is-trunc-map-map-Π :
    (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    (f : (i : I) → A i → B i) →
    ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π f)
  is-trunc-map-map-Π k {I = I} f H h =
    is-trunc-equiv' k
      ( (i : I) → fib (f i) (h i))
      ( equiv-fib-map-Π f h)
      ( is-trunc-Π k (λ i → H i (h i)))

abstract
  is-emb-map-Π :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    {f : (i : I) → A i → B i} →
    ((i : I) → is-emb (f i)) → is-emb (map-Π f)
  is-emb-map-Π {f = f} H =
    is-emb-is-prop-map
      ( is-trunc-map-map-Π neg-one-𝕋 f
        ( λ i → is-prop-map-is-emb (H i)))

emb-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3} →
  ((i : I) → A i ↪ B i) → ((i : I) → A i) ↪ ((i : I) → B i)
pr1 (emb-Π f) = map-Π (λ i → map-emb (f i))
pr2 (emb-Π f) = is-emb-map-Π (λ i → is-emb-map-emb (f i))
```

### A family of truncated maps over any map induces a truncated map on dependent function types

```agda
is-trunc-map-map-Π-is-trunc-map' :
  (k : 𝕋) {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-trunc-map k (f i)) → is-trunc-map k (map-Π' α f)
is-trunc-map-map-Π-is-trunc-map' k {J = J} α f H h =
  is-trunc-equiv' k
    ( (j : J) → fib (f (α j)) (h j))
    ( equiv-fib-map-Π' α f h)
    ( is-trunc-Π k (λ j → H (α j) (h j)))

is-trunc-map-is-trunc-map-map-Π' :
  (k : 𝕋) {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({l : Level} {J : UU l} (α : J → I) → is-trunc-map k (map-Π' α f)) →
  (i : I) → is-trunc-map k (f i)
is-trunc-map-is-trunc-map-map-Π' k {A = A} {B} f H i b =
  is-trunc-equiv' k
    ( fib (map-Π (λ (x : unit) → f i)) (const unit (B i) b))
    ( equiv-Σ
      ( λ a → f i a ＝ b)
      ( equiv-universal-property-unit (A i))
      ( λ h → equiv-ap
        ( equiv-universal-property-unit (B i))
        ( map-Π (λ x → f i) h)
        ( const unit (B i) b)))
    ( H (λ x → i) (const unit (B i) b))

is-emb-map-Π-is-emb' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3} →
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i) →
  ((i : I) → is-emb (f i)) → is-emb (map-Π' α f)
is-emb-map-Π-is-emb' α f H =
  is-emb-is-prop-map
    ( is-trunc-map-map-Π-is-trunc-map' neg-one-𝕋 α f
      ( λ i → is-prop-map-is-emb (H i)))
```

###

```agda
HTPY-map-equiv-Π :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} (B' : A' → UU l2) {A : UU l3} (B : A → UU l4)
  ( e e' : A' ≃ A) (H : htpy-equiv e e') →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
HTPY-map-equiv-Π {A' = A'} B' {A} B e e' H =
  ( f : (a' : A') → B' a' ≃ B (map-equiv e a')) →
  ( f' : (a' : A') → B' a' ≃ B (map-equiv e' a')) →
  ( K : (a' : A') →
        ((tr B (H a')) ∘ (map-equiv (f a'))) ~ (map-equiv (f' a'))) →
  ( map-equiv-Π B e f) ~ (map-equiv-Π B e' f')

htpy-map-equiv-Π-refl-htpy :
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
  ( e : A' ≃ A) →
  HTPY-map-equiv-Π B' B e e (refl-htpy-equiv e)
htpy-map-equiv-Π-refl-htpy {B' = B'} B e f f' K =
  ( htpy-map-Π
    ( λ a →
      ( tr B (is-section-map-inv-is-equiv (is-equiv-map-equiv e) a)) ·l
      ( K (map-inv-is-equiv (is-equiv-map-equiv e) a)))) ·r
  ( precomp-Π (map-inv-is-equiv (is-equiv-map-equiv e)) B')

abstract
  htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e e' : A' ≃ A) (H : htpy-equiv e e') →
    HTPY-map-equiv-Π B' B e e' H
  htpy-map-equiv-Π {B' = B'} B e e' H f f' K =
    ind-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)
      e' H f f' K

  compute-htpy-map-equiv-Π :
    { l1 l2 l3 l4 : Level}
    { A' : UU l1} {B' : A' → UU l2} {A : UU l3} (B : A → UU l4)
    ( e : A' ≃ A) →
    ( htpy-map-equiv-Π {B' = B'} B e e (refl-htpy-equiv e)) ＝
    ( ( htpy-map-equiv-Π-refl-htpy B e))
  compute-htpy-map-equiv-Π {B' = B'} B e =
    compute-ind-htpy-equiv e
      ( HTPY-map-equiv-Π B' B e)
      ( htpy-map-equiv-Π-refl-htpy B e)

map-automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) → ((a : A) → B a)
map-automorphism-Π {B = B} e f =
  ( map-Π (λ a → (map-inv-is-equiv (is-equiv-map-equiv (f a))))) ∘
  ( precomp-Π (map-equiv e) B)

abstract
  is-equiv-map-automorphism-Π :
    { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
    ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
    is-equiv (map-automorphism-Π e f)
  is-equiv-map-automorphism-Π {B = B} e f =
    is-equiv-comp _ _
      ( is-equiv-precomp-Π-is-equiv _ (is-equiv-map-equiv e) B)
      ( is-equiv-map-Π _
        ( λ a → is-equiv-map-inv-is-equiv (is-equiv-map-equiv (f a))))

automorphism-Π :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  ( e : A ≃ A) (f : (a : A) → B a ≃ B (map-equiv e a)) →
  ( (a : A) → B a) ≃ ((a : A) → B a)
pr1 (automorphism-Π e f) = map-automorphism-Π e f
pr2 (automorphism-Π e f) = is-equiv-map-automorphism-Π e f
```

### Precomposing functions `Π B C` by `f : A → B` is `k+1`-truncated if and only if precomposing homotopies is `k`-truncated

```agda
coherence-square-ap-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) {C : B → UU l3}
  (g h : (b : B) → C b) →
  coherence-square-maps
    ( ap (precomp-Π f C) {g} {h})
    ( htpy-eq)
    ( htpy-eq)
    ( precomp-Π f (eq-value g h))
coherence-square-ap-precomp-Π f g .g refl = refl

is-trunc-map-succ-precomp-Π :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  {C : B → UU l3} →
  ((g h : (b : B) → C b) → is-trunc-map k (precomp-Π f (eq-value g h))) →
  is-trunc-map (succ-𝕋 k) (precomp-Π f C)
is-trunc-map-succ-precomp-Π {k = k} {f = f} {C = C} H =
  is-trunc-map-is-trunc-map-ap k (precomp-Π f C)
    ( λ g h →
      is-trunc-map-top-is-trunc-map-bottom-is-equiv k
        ( ap (precomp-Π f C))
        ( htpy-eq)
        ( htpy-eq)
        ( precomp-Π f (eq-value g h))
        ( coherence-square-ap-precomp-Π f g h)
        ( funext g h)
        ( funext (g ∘ f) (h ∘ f))
        ( H g h))
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
