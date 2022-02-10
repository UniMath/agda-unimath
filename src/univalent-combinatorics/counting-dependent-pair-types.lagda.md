# Counting the elements of dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-dependent-pair-types where
```

### `Σ A B` can be counted if `A` can be counted and if each `B x` can be counted

```agda
count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (k : ℕ) (e : Fin k ≃ A) → ((x : A) → count (B x)) → count (Σ A B)
count-Σ' zero-ℕ e f =
  count-is-empty
    ( λ x →
      is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl (pr1 x))
count-Σ' {l1} {l2} {A} {B} (succ-ℕ k) e f =
  count-equiv
    ( ( equiv-Σ-equiv-base B e) ∘e
      ( ( inv-equiv
          ( right-distributive-Σ-coprod (Fin k) unit (B ∘ map-equiv e))) ∘e
        ( equiv-coprod
          ( id-equiv)
          ( inv-equiv
            ( left-unit-law-Σ (B ∘ (map-equiv e ∘ inr)))))))
    ( count-coprod
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star))))

abstract
  equiv-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (k : ℕ) (e : Fin k ≃ A) (f : (x : A) → count (B x)) →
    Fin (number-of-elements-count (count-Σ' k e f)) ≃ Σ A B
  equiv-count-Σ' k e f = pr2 (count-Σ' k e f)

count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count (Σ A B)
pr1 (count-Σ (pair k e) f) = number-of-elements-count (count-Σ' k e f)
pr2 (count-Σ (pair k e) f) = equiv-count-Σ' k e f
```

### We compute the number of elements of a Σ-type

```agda
abstract
  number-of-elements-count-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (k : ℕ) (e : Fin k ≃ A) →
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ' k e f))
      ( sum-Fin-ℕ (λ x → number-of-elements-count (f (map-equiv e x)))) 
  number-of-elements-count-Σ' zero-ℕ e f = refl
  number-of-elements-count-Σ' (succ-ℕ k) e f =
    ( number-of-elements-count-coprod
      ( count-Σ' k id-equiv (λ x → f (map-equiv e (inl x))))
      ( f (map-equiv e (inr star)))) ∙
    ( ap
      ( add-ℕ' (number-of-elements-count (f (map-equiv e (inr star)))))
      ( number-of-elements-count-Σ' k id-equiv (λ x → f (map-equiv e (inl x)))))

abstract
  number-of-elements-count-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (e : count A)
    (f : (x : A) → count (B x)) →
    Id ( number-of-elements-count (count-Σ e f))
      ( sum-count-ℕ e (λ x → number-of-elements-count (f x)))
  number-of-elements-count-Σ (pair k e) f = number-of-elements-count-Σ' k e f
```

### If A and Σ A B can be counted, then each B x can be counted

```agda
count-fiber-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → count (Σ A B) → (x : A) → count (B x)
count-fiber-count-Σ {B = B} e f x =
  count-equiv
    ( equiv-fib-pr1 B x)
    ( count-Σ f
      ( λ z → count-eq (has-decidable-equality-count e) (pr1 z) x))
```

### If Σ A B and each B x can be counted, and if B has a section, then A can be counted

```agda
count-fib-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) →
  (t : Σ A B) → count (fib (map-section b) t)
count-fib-map-section {l1} {l2} {A} {B} b e f (pair y z) =
  count-equiv'
    ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
        ( inv-assoc-Σ A
          ( λ x → Id x y)
          ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
      ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
    ( count-eq (has-decidable-equality-count (f y)) (b y) z)

count-base-count-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  count (Σ A B) → ((x : A) → count (B x)) → count A
count-base-count-Σ b e f =
  count-equiv
    ( equiv-total-fib-map-section b)
    ( count-Σ e (count-fib-map-section b e f))
```

More generally, if `Σ A B` and each `B x` can be counted, then `A` can be counted if and only if the type `Σ A (¬ ∘ B)` can be counted. However, to avoid having to invoke function extensionality, we show that if `Σ A B` and each `B x` can be counted, then `A` can be counted if and only if

```md
   count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))),
```

where `f : (x : A) → count (B x)`. Thus, we have a precise characterization of when the elements of `A` can be counted, if it is given that `Σ A B` and each `B x` can be counted.

```agda
section-count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) →
  (x : A) → coprod (B x) (is-zero-ℕ (number-of-elements-count (f x)))
section-count-base-count-Σ' e f g x with
  is-decidable-is-zero-ℕ (number-of-elements-count (f x))
... | inl p = inr p
... | inr H with is-successor-is-nonzero-ℕ H
... | (pair k p) = inl (map-equiv-count (f x) (tr Fin (inv p) zero-Fin))

count-base-count-Σ' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count (Σ A B) →
  (f : (x : A) → count (B x)) →
  count (Σ A (λ x → is-zero-ℕ (number-of-elements-count (f x)))) → count A
count-base-count-Σ' {l1} {l2} {A} {B} e f g =
  count-base-count-Σ
    ( section-count-base-count-Σ' e f g)
    ( count-equiv'
      ( left-distributive-Σ-coprod A B
        ( λ x → is-zero-ℕ (number-of-elements-count (f x))))
      ( count-coprod e g))
    ( λ x →
      count-coprod
        ( f x)
        ( count-eq has-decidable-equality-ℕ
          ( number-of-elements-count (f x))
          ( zero-ℕ)))
```

### If `A` can be counted and `Σ A P` can be counted for a subtype of `A`, then `P` is decidable

```agda
is-decidable-count-Σ :
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  count X → count (Σ X P) → (x : X) → is-decidable (P x)
is-decidable-count-Σ e f x =
  is-decidable-count (count-fiber-count-Σ e f x)
```
