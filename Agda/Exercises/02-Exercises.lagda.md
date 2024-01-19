# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f p = f (pr₁ p) (pr₂ p)

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] (inl (a , b)) = (inl a , inl b)
[i] (inr c) = (inr c , inr c)

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] (inl a , c) = inl (a , c)
[ii] (inr b , c) = inr (b , c)

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] n = {!!} -- TODO: Understand this.

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] = {!!} -- impossible

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] f g a = g (f a)

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] = {!!}  -- impossible

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!}  -- impossible

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] f a b = f (a , b)

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] = {!!} -- impossible

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] = {!!} -- TODO: Understand this.
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne f a = f (\g → g a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f dna nb = dna (\a → nb (f a))

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f dna nb = dna (\a → f a nb)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)


### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true true eq = id , id
bool-≡-char₁ false false eq = id , id
```


### Exercise 3 (★★)

Using ex. 2, conclude that
```agda
true≢false : ¬ (true ≡ false)
true≢false ()
```
You can actually prove this much easier! How?


### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
false≢true : ¬ (false ≡ true)
false≢true ()

bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true (b→b' , b'→b) = refl true
bool-≡-char₂ true false (b→b' , b'→b) = 𝟘-elim (b→b' ⋆)
bool-≡-char₂ false true (b→b' , b'→b) = 𝟘-elim (b'→b ⋆)
bool-≡-char₂ false false (b→b' , b'→b) = refl false
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char A = (\p → func p , \x y → (\eq → ≡-nondep-elim (\x y → func p x y ≡ true) (prf1 p) x y eq) , prf2 x y p) ,
                            (\p x y → dec-prf p x y)
  where
    func : has-decidable-equality A → A → A → Bool
    func p x y with p x y
    ...           | inl _ = true
    ...           | inr _ = false

    prf1 : (eq : has-decidable-equality A) → (x : A) → func eq x x ≡ true
    prf1 eq x with eq x x
    ...          | (inl p) = refl true
    ...          | (inr p) = 𝟘-elim (p (refl _))

    prf2 : (x y : A)(p : has-decidable-equality A) → func p x y ≡ true → x ≡ y
    prf2 x y p with p x y
    ...           | (inl eq) = \_ → ≡-nondep-elim (\x y → x ≡ y) (\_ → refl _) x y eq

    bool-lemma : (b : Bool) → b ≡ true → b ≡ false → 𝟘
    bool-lemma true _ ()
    bool-lemma false ()

    dec-prf : has-bool-dec-fct A → (x y : A) → is-decidable (x ≡ y)
    dec-prf (f , p) x y with f x y
    ...                    | true = inl (p x y .pr₂ _)
    ...                    | false = inr \eq → bool-lemma _ (p x y .pr₁ eq) _
```
  