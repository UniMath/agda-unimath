# Codiagonals of maps

```agda
module synthetic-homotopy-theory.codiagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.unit-type
open import foundation.commuting-squares-of-maps
open import foundation.action-on-identifications-functions

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.suspension-structures
```

</details>

## Idea

The **codiagonal** of a map `f : A → B` is the unique map `∇ f : B ⊔_A B → B`
equipped with [homotopies](foundation-core.homotopies.md)

```text
  H : ∇ f ∘ inl ~ id
  K : ∇ f ∘ inr ~ id
  L : (H ·r f) ~ (∇ f ·l glue) ∙h (K ·r f)
```

The [fibers](foundation-core.fibers-of-maps.md) of the codiagonal are equivalent
to the [suspensions](synthetic-homotopy-theory.suspensions-of-types.md) of the
fibers of `f`.

## Definitions

### The codiagonal of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  cocone-codiagonal-map : cocone f f B
  pr1 cocone-codiagonal-map = id
  pr1 (pr2 cocone-codiagonal-map) = id
  pr2 (pr2 cocone-codiagonal-map) = refl-htpy

  codiagonal-map : pushout f f → B
  codiagonal-map = cogap f f cocone-codiagonal-map

  compute-inl-codiagonal-map :
    codiagonal-map ∘ inl-pushout f f ~ id
  compute-inl-codiagonal-map =
    compute-inl-cogap f f cocone-codiagonal-map

  compute-inr-codiagonal-map :
    codiagonal-map ∘ inr-pushout f f ~ id
  compute-inr-codiagonal-map =
    compute-inr-cogap f f cocone-codiagonal-map

  compute-glue-codiagonal-map :
    statement-coherence-htpy-cocone f f
      ( cocone-map f f (cocone-pushout f f) codiagonal-map)
      ( cocone-codiagonal-map)
      ( compute-inl-codiagonal-map)
      ( compute-inr-codiagonal-map)
  compute-glue-codiagonal-map =
    compute-glue-cogap f f cocone-codiagonal-map
```

### The codiagonal is the fiberwise suspension

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  private
    P : pushout f f → UU l2
    P x = codiagonal-map f x ＝ b

    c : cocone f f (pushout f f)
    c = cocone-pushout f f

  pushout-1 : {l : Level} →
              universal-property-pushout l
                ( vertical-map-span-flattening-pushout P f f c)
                ( horizontal-map-span-flattening-pushout P f f c)
                ( cocone-flattening-pushout P f f c)
  pushout-1 =
    flattening-lemma-pushout P f f
      ( c)
      ( dependent-up-pushout f f)

  private
    vs = vertical-map-span-flattening-pushout P f f c
    hs = horizontal-map-span-flattening-pushout P f f c
```



```text
                               hs
 Σ A (λ a → P (inl (f a))) --------->  Σ B (λ y → P (inr y))
              |                                 |
              |                                 |
          vs  |                                 |  vc
              |                    ⌜            |
              v                                 v
 Σ B (λ y → P (inl y))     --------->  fiber codiagonal-map b ≡ Σ (pushout f f) P
                               hc
```

```text
                  ϕ
  fiber f b -------------> Σ A (λ a → P (inl (f a)))
     |            ≃                 |
     |                              |
     |                              | vs
     |                         ⌜    |
     v            ≃                 v
   unit     --------------> Σ B (λ y → P (inl y))
                  ψ
```

```agda
  private
    fiber-is-top-left : fiber f b ≃ Σ A (λ a → P (inl-pushout f f (f a)))
    fiber-is-top-left =
      equiv-tot
        ( λ a → equiv-concat (compute-inl-codiagonal-map f (f a)) b)

    ϕ : fiber f b → Σ A (λ a → P (inl-pushout f f (f a)))
    ϕ = map-equiv fiber-is-top-left

    is-equiv-ϕ : is-equiv ϕ
    is-equiv-ϕ = is-equiv-map-equiv fiber-is-top-left

    is-contr-bottom-left : is-contr (Σ B (λ y → P (inl-pushout f f y)))
    is-contr-bottom-left =
      is-contr-equiv
        ( Σ B (λ y → y ＝ b))
        ( equiv-tot
          ( λ y →
            equiv-concat (inv (compute-inl-codiagonal-map f y)) b))
        ( is-contr-total-path' b)

    bottom-left-is-unit : Σ B (λ y → P (inl-pushout f f y)) ≃ unit
    bottom-left-is-unit =
      terminal-map , is-equiv-terminal-map-is-contr is-contr-bottom-left

    ψ : unit → Σ B (λ y → P (inl-pushout f f y))
    ψ = map-inv-equiv bottom-left-is-unit

    is-equiv-ψ : is-equiv ψ
    is-equiv-ψ = is-equiv-map-inv-equiv bottom-left-is-unit

  left-cocone : cocone terminal-map ϕ (Σ B (λ y → P (inl-pushout f f y)))
  left-cocone =
    ψ , vs ,
    ( λ _ → eq-is-prop (is-prop-is-contr is-contr-bottom-left))

  pushout-2 : {l : Level} →
              universal-property-pushout l
                ( terminal-map)
                ( ϕ)
                ( left-cocone)
  pushout-2 =
    universal-property-pushout-is-equiv'
      ( terminal-map)
      ( ϕ)
      ( left-cocone)
      ( is-equiv-ϕ)
      ( is-equiv-ψ)

  private
    hc = horizontal-map-cocone-flattening-pushout P f f c
    vc = vertical-map-cocone-flattening-pushout P f f c
    c' : cocone terminal-map (hs ∘ ϕ) (Σ (pushout f f) P)
    c' = hc ∘ ψ ,
         vc ,
         ( λ x → concat (foo x) ((vc ∘ hs ∘ ϕ) x)
                             (coherence-square-cocone-flattening-pushout P f f c (ϕ x)))
      where
        foo : (x : fiber f b) →
              ((hc ∘ ψ) ∘ terminal-map) x ＝ (hc ∘ vs) (ϕ x)
        foo x = ap hc (eq-is-prop (is-prop-is-contr is-contr-bottom-left))

  pushout-3 : {l : Level} →
              universal-property-pushout l
                ( terminal-map)
                ( hs ∘ ϕ)
                c'
  pushout-3 =
    universal-property-pushout-rectangle-universal-property-pushout-right
      ( terminal-map)
      ( ϕ)
      ( hs)
      ( left-cocone)
      ( cocone-flattening-pushout P f f c)
      pushout-2
      pushout-1
```

```text
               hs ∘ ϕ
  fiber f b -------------> Σ B (λ y → P (inr y))
     |                              |
     |                              |
     |                              | vc
     |                      ⌜       |
     v                              v
   unit     --------------> fiber codiagonal-map b ≡ Σ (pushout f f) P
                hc ∘ ψ
```

```text

  fiber f b ------------------->  unit
     |                              |
     |                              |
  id | ≃                          ≃ | χ
     |                      ⌜       |
     v                              v
  fiber f b --------------> Σ B (λ y → P (inr y))
                hs ∘ ϕ
```

```agda
  private
    is-contr-top-right : is-contr (Σ B (λ y → P (inr-pushout f f y)))
    is-contr-top-right =
      is-contr-equiv
        ( Σ B (λ y → y ＝ b))
        ( equiv-tot
          ( λ y →
            equiv-concat (inv (compute-inr-codiagonal-map f y)) b))
        ( is-contr-total-path' b)

    top-right-is-unit : Σ B (λ y → P (inr-pushout f f y)) ≃ unit
    top-right-is-unit =
      terminal-map , is-equiv-terminal-map-is-contr is-contr-top-right

    χ : unit → Σ B (λ y → P (inr-pushout f f y))
    χ = map-inv-equiv top-right-is-unit

    is-equiv-χ : is-equiv χ
    is-equiv-χ = is-equiv-map-inv-equiv top-right-is-unit

  top-cocone : cocone id terminal-map (Σ B (λ y → P (inr-pushout f f y)))
  top-cocone = hs ∘ ϕ , χ , (λ _ → eq-is-prop (is-prop-is-contr is-contr-top-right))
    {- χ , hs ,
    ( λ _ → eq-is-prop (is-prop-is-contr is-contr-top-right)) -}

  pushout-4 : {l : Level} →
              universal-property-pushout l
                ( id)
                ( terminal-map)
                ( top-cocone)
  pushout-4 =
    universal-property-pushout-is-equiv
      ( id)
      ( terminal-map)
      ( top-cocone)
      ( is-equiv-id)
      ( is-equiv-χ)

  private
    c'' : cocone terminal-map terminal-map (Σ (pushout f f) P)
    c'' = hc ∘ ψ , vc ∘ χ ,
      (λ x → equational-reasoning
                hc (ψ (star))
                  ＝ vc (hs (ϕ x)) by (coherence-square-cocone terminal-map (hs ∘ ϕ) c' x)
                  ＝ vc (χ star) by (ap vc (eq-is-prop (is-prop-is-contr is-contr-top-right))))
    -- hc ∘ ψ , vc ∘ χ , (λ x → {!!})
-- ((hc ∘ ψ) ∘ terminal-map) x ＝ ((vc ∘ χ) ∘ terminal-map) x

  pushout-5 : {l : Level} →
              universal-property-pushout l
                ( terminal-map)
                ( terminal-map)
                c''
  pushout-5 =
    universal-property-pushout-rectangle-universal-property-pushout-top
      ( id)
      ( terminal-map)
      ( terminal-map)
      ( top-cocone)
      ( c')
      ( pushout-4)
      ( pushout-3)

```
